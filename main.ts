// Fresh-burst scalper for the pump.fun paper replay (agent-fun/replay/v2).
//
// The harness speaks a tiny line protocol: one `hello` first (capital, caps,
// latency in slots, fees, seed), then one `batch` per slot carrying that
// slot's events, marks and fills, and this bot answers each batch with one
// reply holding its `orders` for that slot. Orders decided on a batch fill
// two slots later. Everything below is a pure function of the hello/batch
// stream: no clock, no environment, no randomness, so two runs of the same
// window produce byte-identical action logs.
//
// Idea: pump.fun bonding curves either catch a burst of early buying or fade
// to nothing. This bot only buys young curves (created 8-300 slots ago)
// while a short burst is actually happening — several distinct buyers,
// net SOL flowing in, price rising and sitting near its burst high —
// stakes a fixed 0.06 SOL once per curve, never adds, and gets out fast:
// a -12% stop-loss, a trailing stop once the position is +6%, a +40% hard
// take-profit, a 450-slot time limit, or a fade in buy flow. With at most
// 5 open positions the bot rotates through many coins, which is also what
// the guardrail wants: at least 20 distinct coins with a >= 0.01 SOL round
// trip each. A pace probe (a 0.02 SOL buy sold on the next batch) fires
// only if the distinct-coin count is lagging late in the window.

import {
  LAMPORTS_PER_SOL,
  runBot,
  type Batch,
  type BotState,
  type OrderInput,
  type Pubkey,
} from './vendor/makefun-bot.ts';

const LAMPORTS = 1e9;
// Curve fee on every trade: 0.95% protocol + 0.30% creator (fallbacks).
const CURVE_FEE = 0.0125;

// ---- tunables (SOL / slots / fractions, all in plain numbers) ----
const ENTRY_MIN_AGE = 8; // slots since CreateEvent before a buy is allowed
const ENTRY_MAX_AGE = 300; // ... and after this the burst is stale
const ENTRY_WINDOW = 10; // slots of tape the burst is measured over
const ENTRY_MIN_BUYS = 4; // buy trades inside the window
const ENTRY_MIN_BUYERS = 3; // distinct buying wallets inside the window
const ENTRY_MIN_NET_SOL = 0.2; // net SOL inflow (buys minus sells) in window
const ENTRY_MIN_UP = 0.02; // price rise over the window, as a fraction
const ENTRY_NEAR_HIGH = 0.97; // last price vs the window high
const ENTRY_MIN_RQ_SOL = 0.3; // real SOL reserves at entry, lower bound
const ENTRY_MAX_RQ_SOL = 25; // ... upper bound (already too big to burst)
const STAKE_SOL = 0.06; // fixed buy size per coin
const MIN_BUY_SOL = 0.01; // guardrail round-trip floor; smaller buys are skipped
const BUY_SLIP_BPS = 1000; // 10% slippage allowance on buys
const SELL_SLIP_BPS = 10000; // sells always go out: exit certainty beats price
const STOP_LOSS = 0.12; // sell when close value < cost * (1 - STOP_LOSS)
const TRAIL_ARM = 0.06; // trailing stop arms once value >= cost * (1 + TRAIL_ARM)
const TRAIL_GIVEBACK = 0.15; // ... then sells when value < peak * (1 - TRAIL_GIVEBACK)
const TAKE_PROFIT = 0.4; // hard sell at value >= cost * (1 + TAKE_PROFIT)
const MAX_HOLD_SLOTS = 450; // time-limit exit
const FADE_WINDOW = 8; // slots of tape the fade is measured over
const FADE_NET_SOL = -0.25; // sell when net flow over FADE_WINDOW is below this
const PROBE_SOL = 0.02; // guardrail probe buy size
const PROBE_AFTER_SLOTS = 12000; // probe only once this far into the window
const PROBE_TARGET_COINS = 20; // ... and only while distinct coins are below this
const TAPE_KEEP_SLOTS = 700; // trades older than this are pruned

interface TapeTrade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  trades: TapeTrade[];
}

interface Held {
  opened: number;
  peakValueSol: number;
  exiting: boolean;
}

const tapes = new Map<Pubkey, Tape>();
/** Curves this bot has ever bought (one entry per curve, ever). */
const entered = new Set<Pubkey>();
/** Open momentum positions, by mint. */
const held = new Map<Pubkey, Held>();
/** Guardrail probe mints: true once the probe buy has filled and must be sold. */
const probes = new Map<Pubkey, boolean>();
/** Distinct mints this bot's own filled orders touched (harness closes excluded). */
const myCoins = new Set<Pubkey>();
let myFills = 0;
let firstSlot = -1;

function tapeOf(mint: Pubkey): Tape {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [] };
    tapes.set(mint, t);
  }
  return t;
}

/** Price of one token in SOL from virtual reserves (quote / token). */
function priceOf(vq: bigint, vt: bigint): number {
  const token = Number(vt);
  if (token <= 0) return 0;
  return Number(vq) / token;
}

/** Net SOL flow (buys minus sells) on a tape over the last `w` slots. */
function netFlow(t: Tape, now: number, w: number): number {
  let net = 0;
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= now - w) break;
    net += tr.buy ? tr.sol : -tr.sol;
  }
  return net;
}

/** True when the tape shows a fresh buying burst right now. */
function burstSignal(t: Tape, now: number, rqSol: number): boolean {
  if (rqSol < ENTRY_MIN_RQ_SOL || rqSol > ENTRY_MAX_RQ_SOL) return false;
  if (t.created === null) return false;
  const age = now - t.created;
  if (age < ENTRY_MIN_AGE || age > ENTRY_MAX_AGE) return false;
  const from = now - ENTRY_WINDOW;
  let buys = 0;
  let buySol = 0;
  let sellSol = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const buyers = new Set<string>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    if (tr.buy) {
      buys++;
      buySol += tr.sol;
      buyers.add(tr.user);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buys < ENTRY_MIN_BUYS || buyers.size < ENTRY_MIN_BUYERS) return false;
  if (buySol - sellSol < ENTRY_MIN_NET_SOL) return false;
  if (startPrice <= 0 || last <= 0 || high <= 0) return false;
  if (last / startPrice - 1 < ENTRY_MIN_UP) return false;
  if (last < high * ENTRY_NEAR_HIGH) return false;
  return true;
}

/** What selling `tokens` now would return, in SOL, after curve and tx fees. */
function closeValueSol(
  state: BotState,
  batch: Batch,
  mint: Pubkey,
  tokens: number,
): number {
  const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
  const mk = marks.get(mint);
  const curve = state.curves.get(mint);
  const vq =
    mk !== undefined
      ? Number(mk.virtual_quote_reserves)
      : curve !== undefined
        ? Number(curve.virtual_quote_reserves)
        : 0;
  const vt =
    mk !== undefined
      ? Number(mk.virtual_token_reserves)
      : curve !== undefined
        ? Number(curve.virtual_token_reserves)
        : 0;
  if (vq <= 0 || vt <= 0) return 0;
  const gross = (tokens * vq) / (vt + tokens) / LAMPORTS;
  return gross * (1 - CURVE_FEE) - Number(state.txFeeLamports()) / LAMPORTS;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    if (firstSlot < 0) firstSlot = now;
    const elapsed = now - firstSlot;
    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const txSol = Number(state.txFeeLamports()) / LAMPORTS;

    // Fold this batch's fills and events into the tapes.
    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFills++;
        myCoins.add(f.mint);
      }
    }
    const traded = new Set<Pubkey>();
    for (const e of batch.events) {
      if (e.event === 'CreateEvent') {
        tapeOf(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol: Number(e.sol_amount) / LAMPORTS,
          user: e.user,
          price: priceOf(BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves)),
        });
        traded.add(e.mint);
      }
    }
    for (const mint of traded) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - TAPE_KEEP_SLOTS) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }

    const pendingByMint = new Map<Pubkey, { buy: boolean; sell: boolean }>();
    for (const po of state.pending.values()) {
      const rec = pendingByMint.get(po.order.mint) ?? { buy: false, sell: false };
      if (po.order.side === 'buy') rec.buy = true;
      else rec.sell = true;
      pendingByMint.set(po.order.mint, rec);
    }
    const sellNow = (mint: Pubkey, tokenAmount: string): boolean => {
      if (orders.length >= cap) return false;
      orders.push({ side: 'sell', mint, token_amount: tokenAmount, max_slippage_bps: SELL_SLIP_BPS });
      return true;
    };

    // 1. Exits first: every held position is re-priced and sold on the first
    //    exit rule that fires.
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) held.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete) continue;
      const tokens = Number(pos.token_amount);
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      const value = closeValueSol(state, batch, mint, tokens);
      if (value > h.peakValueSol) h.peakValueSol = value;
      let exit = h.exiting;
      if (!exit && value < cost * (1 - STOP_LOSS)) exit = true;
      if (!exit && value >= cost * (1 + TAKE_PROFIT)) exit = true;
      if (!exit && h.peakValueSol >= cost * (1 + TRAIL_ARM) && value < h.peakValueSol * (1 - TRAIL_GIVEBACK)) exit = true;
      if (!exit && now - h.opened > MAX_HOLD_SLOTS) exit = true;
      if (!exit && netFlow(tapeOf(mint), now, FADE_WINDOW) < FADE_NET_SOL) exit = true;
      if (!exit) continue;
      h.exiting = true;
      if (pendingByMint.get(mint)?.sell) continue;
      sellNow(mint, pos.token_amount);
    }

    // 2. Probe exits: a probe buy is sold whole on the first batch after it lands.
    for (const [mint, filled] of probes) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (!filled || curve === undefined || curve.complete) continue;
      if (pendingByMint.get(mint)?.sell) continue;
      if (sellNow(mint, pos.token_amount)) probes.set(mint, true);
    }
    // A probe whose buy filled this batch becomes sellable next batch.
    for (const f of batch.fills) {
      if (f.status === 'filled' && probes.has(f.mint) && !f.client_id.startsWith('_')) {
        probes.set(f.mint, true);
      }
    }

    // 3. Entries: one fixed-size buy per bursting young curve.
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    for (const mint of traded) {
      if (orders.length >= cap || slotsLeft <= 0) break;
      if (entered.has(mint) || held.has(mint) || probes.has(mint)) continue;
      if (pendingByMint.has(mint)) continue;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      if (!burstSignal(tapeOf(mint), now, rqSol)) continue;
      const capLamports = state.maxBuyLamports(mint);
      const stakeLamports = BigInt(Math.floor(STAKE_SOL * LAMPORTS));
      const amount = capLamports < stakeLamports ? capLamports : stakeLamports;
      if (amount < BigInt(Math.floor(MIN_BUY_SOL * LAMPORTS))) continue;
      if (free < Number(amount) / LAMPORTS + txSol) continue;
      orders.push({ side: 'buy', mint, quote_lamports: amount, max_slippage_bps: BUY_SLIP_BPS });
      entered.add(mint);
      held.set(mint, { opened: now, peakValueSol: 0, exiting: false });
      free -= Number(amount) / LAMPORTS + txSol;
      slotsLeft--;
    }

    // 4. Guardrail probe: late in the window, if distinct coins lag the
    //    20-coin bar, buy a small probe of the most liquid curve traded
    //    this batch and sell it on the next batch.
    if (
      probes.size === 0 &&
      slotsLeft > 0 &&
      elapsed > PROBE_AFTER_SLOTS &&
      myCoins.size < PROBE_TARGET_COINS &&
      orders.length < cap
    ) {
      let best: Pubkey | null = null;
      let bestRq = -1;
      for (const mint of traded) {
        if (entered.has(mint) || held.has(mint) || state.positions.has(mint)) continue;
        if (pendingByMint.has(mint)) continue;
        const curve = state.curves.get(mint);
        if (curve === undefined || curve.complete) continue;
        const rq = Number(curve.real_quote_reserves);
        if (rq > bestRq) {
          bestRq = rq;
          best = mint;
        }
      }
      if (best !== null) {
        const amount = BigInt(Math.floor(PROBE_SOL * LAMPORTS));
        if (state.maxBuyLamports(best) >= amount && free >= PROBE_SOL + 2 * txSol) {
          orders.push({ side: 'buy', mint: best, quote_lamports: amount, max_slippage_bps: BUY_SLIP_BPS });
          entered.add(best);
          probes.set(best, false);
        }
      }
    }

    return orders;
  },
});
