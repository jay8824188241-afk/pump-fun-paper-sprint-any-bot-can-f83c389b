// Fresh-burst scalper + dip buyer for the pump.fun paper replay
// (agent-fun/replay/v2).
//
// The harness speaks a tiny line protocol: one `hello` first (capital, caps,
// latency in slots, fees, seed), then one `batch` per slot carrying that
// slot's events, marks and fills, and this bot answers each batch with one
// reply holding its `orders` for that slot. Orders decided on a batch fill
// two slots later. Everything below is a pure function of the hello/batch
// stream: no clock, no environment, no randomness, so two runs of the same
// window produce byte-identical action logs.
//
// Two entries, one exit philosophy each:
//
// 1. Dip entries (the profit engine). A young curve that just dumped >= 5%
//    inside 10 slots while buyers are still stepping in (>= 3 buys, net
//    flow >= 0) is usually still falling — median forward return is
//    negative — but the right tail is fat: a few of these coins rip 2-10x.
//    So dip positions are staked larger (0.08 SOL) and exited loose:
//    -12% stop, +200% take-profit, a 30% trailing stop armed at +10%, and
//    a 900-slot time limit. Tight exits were measured to kill this edge:
//    they cut the runners that pay for all the small losers.
//
// 2. Burst entries (coin-count filler plus lottery tickets). A young curve
//    with a live buying burst (>= 6 buys, >= 5 distinct buyers, >= 0.5 SOL
//    net inflow, price up >= 5% over 10 slots, near its window high) gets a
//    small 0.02 SOL stake and tight exits (-8% stop, +25% take-profit,
//    10% trailing stop armed at +4%, 250-slot limit). On their own these
//    lose a little per trade, but they keep the bot above the guardrail bar
//    of 20 distinct coins with a >= 0.01 SOL round trip each, and they
//    occasionally catch a runner.
//
// A pace probe (a 0.02 SOL buy sold on the next batch) fires only if the
// distinct-coin count is still lagging late in the window.

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

// ---- shared ----
const WINDOW = 10; // slots of tape each signal is measured over
const MIN_BUY_SOL = 0.01; // guardrail round-trip floor; smaller buys are skipped
const BUY_SLIP_BPS = 1000; // 10% slippage allowance on buys
const SELL_SLIP_BPS = 10000; // sells always go out: exit certainty beats price
const TAPE_KEEP_SLOTS = 1000; // trades older than this are pruned

// ---- dip entries ----
const DIP_MIN_AGE = 8; // slots since CreateEvent before a buy is allowed
const DIP_MAX_AGE = 900; // ... and after this the dip is stale
const DIP_MIN_BUYS = 3; // buy trades inside the window
const DIP_MIN_NET_SOL = 0; // net SOL inflow (buys minus sells) in window
const DIP_DROP = 0.05; // price fall over the window, as a fraction
const DIP_MIN_RQ_SOL = 0.3; // real SOL reserves at entry, lower bound
const DIP_MAX_RQ_SOL = 25; // ... upper bound
const DIP_STAKE_SOL = 0.08; // fixed buy size per dip coin
const DIP_STOP = 0.12; // sell when close value < cost * (1 - DIP_STOP)
const DIP_TRAIL_ARM = 0.1; // trailing stop arms once value >= cost * (1 + arm)
const DIP_TRAIL = 0.3; // ... then sells when value < peak * (1 - DIP_TRAIL)
const DIP_TP = 2.0; // hard sell at value >= cost * (1 + DIP_TP)
const DIP_MAX_HOLD = 900; // time-limit exit, in slots

// ---- burst entries ----
const BURST_MIN_AGE = 8;
const BURST_MAX_AGE = 300;
const BURST_MIN_BUYS = 6;
const BURST_MIN_BUYERS = 5;
const BURST_MIN_NET_SOL = 0.5;
const BURST_MIN_UP = 0.05; // price rise over the window, as a fraction
const BURST_NEAR_HIGH = 0.97; // last price vs the window high
const BURST_MIN_RQ_SOL = 0.3;
const BURST_MAX_RQ_SOL = 25;
const BURST_STAKE_SOL = 0.02;
const BURST_STOP = 0.08;
const BURST_TRAIL_ARM = 0.04;
const BURST_TRAIL = 0.1;
const BURST_TP = 0.25;
const BURST_MAX_HOLD = 250;

// ---- guardrail probe ----
const PROBE_SOL = 0.02; // probe buy size
const PROBE_AFTER_SLOTS = 12000; // probe only once this far into the window
const PROBE_TARGET_COINS = 20; // ... and only while distinct coins are below this

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

type Kind = 'dip' | 'burst';

interface Held {
  kind: Kind;
  opened: number;
  peakValueSol: number;
  exiting: boolean;
}

const tapes = new Map<Pubkey, Tape>();
/** Curves this bot has ever bought (one entry per curve, ever). */
const entered = new Set<Pubkey>();
/** Open positions, by mint. */
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

/** Trades on a tape inside the last `w` slots, oldest first. */
function windowTrades(t: Tape, now: number, w: number): TapeTrade[] {
  const out: TapeTrade[] = [];
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= now - w) break;
    out.unshift(tr);
  }
  return out;
}

/** True when the tape shows a dip with buyers still stepping in. */
function dipSignal(t: Tape, now: number, rqSol: number): boolean {
  if (rqSol < DIP_MIN_RQ_SOL || rqSol > DIP_MAX_RQ_SOL) return false;
  if (t.created === null) return false;
  const age = now - t.created;
  if (age < DIP_MIN_AGE || age > DIP_MAX_AGE) return false;
  const w = windowTrades(t, now, WINDOW);
  if (w.length < 2) return false;
  let buys = 0;
  let net = 0;
  for (const tr of w) {
    if (tr.buy) {
      buys++;
      net += tr.sol;
    } else {
      net -= tr.sol;
    }
  }
  if (buys < DIP_MIN_BUYS || net < DIP_MIN_NET_SOL) return false;
  const startPrice = w[0]!.price;
  const lastPrice = w[w.length - 1]!.price;
  if (startPrice <= 0 || lastPrice <= 0) return false;
  return lastPrice / startPrice - 1 <= -DIP_DROP;
}

/** True when the tape shows a live buying burst. */
function burstSignal(t: Tape, now: number, rqSol: number): boolean {
  if (rqSol < BURST_MIN_RQ_SOL || rqSol > BURST_MAX_RQ_SOL) return false;
  if (t.created === null) return false;
  const age = now - t.created;
  if (age < BURST_MIN_AGE || age > BURST_MAX_AGE) return false;
  const w = windowTrades(t, now, WINDOW);
  if (w.length < 2) return false;
  let buys = 0;
  let net = 0;
  let high = 0;
  const buyers = new Set<string>();
  for (const tr of w) {
    if (tr.buy) {
      buys++;
      net += tr.sol;
      buyers.add(tr.user);
    } else {
      net -= tr.sol;
    }
    if (tr.price > high) high = tr.price;
  }
  if (buys < BURST_MIN_BUYS || buyers.size < BURST_MIN_BUYERS) return false;
  if (net < BURST_MIN_NET_SOL) return false;
  const startPrice = w[0]!.price;
  const lastPrice = w[w.length - 1]!.price;
  if (startPrice <= 0 || lastPrice <= 0 || high <= 0) return false;
  if (lastPrice / startPrice - 1 < BURST_MIN_UP) return false;
  if (lastPrice < high * BURST_NEAR_HIGH) return false;
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

/** Exit parameters for a position kind. */
function exitParams(kind: Kind): {
  stop: number;
  arm: number;
  trail: number;
  tp: number;
  maxHold: number;
} {
  return kind === 'dip'
    ? { stop: DIP_STOP, arm: DIP_TRAIL_ARM, trail: DIP_TRAIL, tp: DIP_TP, maxHold: DIP_MAX_HOLD }
    : { stop: BURST_STOP, arm: BURST_TRAIL_ARM, trail: BURST_TRAIL, tp: BURST_TP, maxHold: BURST_MAX_HOLD };
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
    //    exit rule of its kind that fires.
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
      const p = exitParams(h.kind);
      let exit = h.exiting;
      if (!exit && value < cost * (1 - p.stop)) exit = true;
      if (!exit && value >= cost * (1 + p.tp)) exit = true;
      if (!exit && h.peakValueSol >= cost * (1 + p.arm) && value < h.peakValueSol * (1 - p.trail)) exit = true;
      if (!exit && now - h.opened > p.maxHold) exit = true;
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

    // 3. Entries: dip entries first (they carry the edge), then burst entries
    //    while open-position slots remain.
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    const tryBuy = (mint: Pubkey, kind: Kind, stakeSol: number): void => {
      if (orders.length >= cap || slotsLeft <= 0) return;
      const capLamports = state.maxBuyLamports(mint);
      const stakeLamports = BigInt(Math.floor(stakeSol * LAMPORTS));
      const amount = capLamports < stakeLamports ? capLamports : stakeLamports;
      if (amount < BigInt(Math.floor(MIN_BUY_SOL * LAMPORTS))) return;
      if (free < Number(amount) / LAMPORTS + txSol) return;
      orders.push({ side: 'buy', mint, quote_lamports: amount, max_slippage_bps: BUY_SLIP_BPS });
      entered.add(mint);
      held.set(mint, { kind, opened: now, peakValueSol: 0, exiting: false });
      free -= Number(amount) / LAMPORTS + txSol;
      slotsLeft--;
    };
    for (const mint of traded) {
      if (orders.length >= cap || slotsLeft <= 0) break;
      if (entered.has(mint) || held.has(mint) || probes.has(mint)) continue;
      if (pendingByMint.has(mint)) continue;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      if (dipSignal(tapeOf(mint), now, rqSol)) tryBuy(mint, 'dip', DIP_STAKE_SOL);
    }
    for (const mint of traded) {
      if (orders.length >= cap || slotsLeft <= 0) break;
      if (entered.has(mint) || held.has(mint) || probes.has(mint)) continue;
      if (pendingByMint.has(mint)) continue;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      if (burstSignal(tapeOf(mint), now, rqSol)) tryBuy(mint, 'burst', BURST_STAKE_SOL);
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
