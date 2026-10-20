/* Online Bluff.
   Same networking approach as tictactoe.js: PeerJS (WebRTC), host peer ID derived from the
   room code. The host is the referee: it shuffles, deals, validates every action and is the
   only device that ever holds every hand. Each guest is sent only their own cards plus
   public information (card counts, pile size, whose turn it is).

   RULES IN BRIEF
   - A round is one circuit of the table. The round's starter declares a RANK and plays any
     number of cards face down as that rank.
   - Everyone after them either plays any number of cards (all claimed as that same rank,
     truthfully or not) or passes. The round ends once the player before the starter has acted.
   - Anyone can call "Bluff!" after a play, until the next player acts. A liar takes the whole
     pile and the challenger starts the next round. A wrong caller takes the pile and the
     accused starts the next round.
   - If nobody calls, the pile is burned and the same starter leads again with any rank.
   - First player to empty their hand wins, provided their last play survives a call.

   Tweakable numbers are in RULES. The rules themselves live in applyPlay / applyPass /
   applyCall. */

const RULES = {
    minPlayers: 2,
    maxPlayers: 8,
    maxCards: null,        // most cards anyone may play in one turn (null = no limit)
    callWindowMs: 1200,    // after a play, the next player must wait this long so others can call
    decksFor: (players) => (players >= 7 ? 2 : 1)
};

const ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"; // no 0/O/1/I
const PREFIX = "minimaliser-bluff-";
const CODE_LENGTH = 5;
const MAX_NAME = 14;

const RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"];
const RANK_NAMES = ["Aces", "Twos", "Threes", "Fours", "Fives", "Sixes", "Sevens", "Eights", "Nines", "Tens", "Jacks", "Queens", "Kings"];
const RANK_SINGULAR = ["Ace", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine", "Ten", "Jack", "Queen", "King"];
const SUITS = ["♠", "♥", "♦", "♣"]; // spades, hearts, diamonds, clubs
const SUIT_NAMES = ["spades", "hearts", "diamonds", "clubs"];
const RED_SUIT = [false, true, true, false];

const $ = (id) => document.getElementById(id);
const VIEWS = ["lobby", "joinView", "roomView", "gameView"];

let peer = null;
let conn = null;            // guest -> host
let role = null;            // "host" | "guest"
let roomCode = "";
let myName = "";
let hostAttempts = 0;

let game = null;            // host only: the full truth
const conns = new Map();    // host only: pid -> DataConnection
let nextPid = 1;

let view = null;            // what this device is allowed to see
let shown = null;
let handKey = "";
let declRank = null;        // rank the starter has chosen to declare
const selected = new Set();

/* =====================================================================
   CARDS & RANDOMNESS
   ===================================================================== */
function cardRank(id) { return id % 13; }
function cardSuit(id) { return Math.floor(id / 13) % 4; }
function byRankThenSuit(a, b) { return cardRank(a) - cardRank(b) || cardSuit(a) - cardSuit(b) || a - b; }

function randInt(n) {
    const limit = Math.floor(0x100000000 / n) * n;
    const buf = new Uint32Array(1);
    let x;
    do { crypto.getRandomValues(buf); x = buf[0]; } while (x >= limit);
    return x % n;
}

function shuffle(list) {
    for (let i = list.length - 1; i > 0; i--) {
        const j = randInt(i + 1);
        [list[i], list[j]] = [list[j], list[i]];
    }
    return list;
}

function makeCode() {
    let code = "";
    for (let i = 0; i < CODE_LENGTH; i++) code += ALPHABET[randInt(ALPHABET.length)];
    return code;
}

/* =====================================================================
   GAME ENGINE (host only mutates)
   ===================================================================== */
function newGame() {
    return {
        phase: "lobby",       // "lobby" | "playing" | "over"
        players: [],          // seat order: { pid, name, hand, out }
        turn: null,
        starter: null,        // leads the current round
        lock: null,           // { rankIndex } set by the starter; null until declared
        roundOver: false,     // the circuit is complete and the starter is to lead again
        pile: [],
        lastPlay: null,       // { by, cards, rankIndex }: the play that can still be called
        playAt: 0,            // when lastPlay happened (for callWindowMs)
        pendingWin: null,     // player who just played their last cards, not yet challenged
        result: null,         // most recent challenge
        winner: null,
        endReason: "",
        log: []
    };
}

// NOTE: player ids start at 0 (the host), so never test an id for truthiness; compare with null.
const seat = (pid) => game.players.find((p) => p.pid === pid);
const activePlayers = () => game.players.filter((p) => !p.out);
const fail = (error) => ({ ok: false, error });

function nextActive(pid) {
    const list = game.players;
    const start = list.findIndex((p) => p.pid === pid);
    for (let k = 1; k <= list.length; k++) {
        const p = list[(start + k) % list.length];
        if (!p.out) return p.pid;
    }
    return pid;
}

function note(entry) {
    game.log.push(entry);
    if (game.log.length > 8) game.log.shift();
}

// The starter must (re)declare when no lock is set yet, or the circuit has just finished.
function isDeclaring() {
    return game.turn === game.starter && (game.lock === null || game.roundOver);
}

// Others get a moment to call bluff before the next player can act on a fresh play.
function tooSoon() {
    return game.lastPlay !== null && Date.now() - game.playAt < RULES.callWindowMs;
}

function burnPile() {
    if (game.pile.length) note({ t: "burn", count: game.pile.length });
    game.pile = [];
}

// Move play on from `pid`; if that completes the circuit, the round is over.
function advanceFrom(pid) {
    const next = nextActive(pid);
    if (next === game.starter) {
        game.roundOver = true;
        game.turn = game.starter;
        // Nothing left to challenge, so the pile burns now. Otherwise it burns when the
        // starter leads again (or goes to whoever loses a call).
        if (game.lastPlay === null) burnPile();
    } else {
        game.turn = next;
    }
}

function addPlayer(pid, rawName) {
    let base = String(rawName || "").replace(/\s+/g, " ").trim().slice(0, MAX_NAME) || `Player ${pid + 1}`;
    let name = base, n = 2;
    while (game.players.some((p) => p.name.toLowerCase() === name.toLowerCase())) name = `${base} ${n++}`;
    game.players.push({ pid, name, hand: [], out: false });
}

function dealGame() {
    game.players = game.players.filter((p) => !p.out);
    const n = game.players.length;
    const deck = shuffle(Array.from({ length: 52 * RULES.decksFor(n) }, (_, i) => i));
    game.players.forEach((p) => { p.hand = []; });
    deck.forEach((id, i) => game.players[i % n].hand.push(id));
    game.players.forEach((p) => p.hand.sort(byRankThenSuit));

    const starter = game.players[randInt(n)].pid;
    Object.assign(game, {
        phase: "playing", pile: [], lastPlay: null, playAt: 0, pendingWin: null, result: null,
        winner: null, endReason: "", lock: null, roundOver: false, log: [],
        starter, turn: starter
    });
}

function finish(pid, reason) {
    game.phase = "over";
    game.winner = pid;
    game.pendingWin = null;
    game.endReason = reason || "";
}

function applyPlay(pid, cards, rankIndex) {
    if (game.phase !== "playing") return fail("The game isn't running.");
    if (game.turn !== pid) return fail("It isn't your turn.");
    if (game.pendingWin !== null) return fail("Call the bluff or let it stand first.");
    if (tooSoon()) return fail("Hold on, others can still call bluff.");
    if (!Array.isArray(cards) || cards.length < 1) return fail("Pick at least one card.");

    const me = seat(pid);
    const unique = new Set(cards);
    if (unique.size !== cards.length || !cards.every((c) => Number.isInteger(c) && me.hand.includes(c))) {
        return fail("Those cards aren't in your hand.");
    }

    const declaring = isDeclaring();
    if (declaring && (!Number.isInteger(rankIndex) || rankIndex < 0 || rankIndex > 12)) return fail("Choose a rank to declare.");
    if (RULES.maxCards && cards.length > RULES.maxCards) return fail(`You can play up to ${RULES.maxCards} cards at once.`);

    // All checks passed: apply.
    if (declaring) {
        if (game.roundOver) burnPile();                 // the previous round ends here
        game.lock = { rankIndex };
        game.roundOver = false;
        game.starter = pid;
        game.result = null;
    }

    me.hand = me.hand.filter((c) => !unique.has(c));
    game.pile.push(...cards);
    game.lastPlay = { by: pid, cards: cards.slice(), rankIndex: game.lock.rankIndex };
    game.playAt = Date.now();
    note({ t: "play", by: pid, count: cards.length, rank: game.lock.rankIndex, starts: declaring });
    if (me.hand.length === 0) game.pendingWin = pid;

    advanceFrom(pid);
    return { ok: true };
}

function applyPass(pid) {
    if (game.phase !== "playing" || game.turn !== pid) return fail("It isn't your turn.");

    if (game.pendingWin !== null) {                     // "let it stand": nobody called
        if (tooSoon()) return fail("Hold on, others can still call bluff.");
        finish(game.pendingWin);
        return { ok: true };
    }
    if (isDeclaring()) return fail("You lead this round, so you have to play.");
    if (tooSoon()) return fail("Hold on, others can still call bluff.");

    game.lastPlay = null;                               // a pass closes the window to call
    note({ t: "pass", by: pid });
    advanceFrom(pid);
    return { ok: true };
}

function applyCall(pid) {
    if (game.phase !== "playing") return fail("The game isn't running.");
    const caller = seat(pid);
    if (!caller || caller.out) return fail("You're not in this game.");
    const lp = game.lastPlay;
    if (!lp) return fail("There's nothing to call right now.");
    if (lp.by === pid) return fail("You can't call your own play.");

    const truthful = lp.cards.every((c) => cardRank(c) === lp.rankIndex);
    const loserPid = truthful ? pid : lp.by;            // wrong caller, or caught bluffer
    const starterPid = truthful ? lp.by : pid;          // the other one leads next
    const loser = seat(loserPid);
    const picked = game.pile.length;

    loser.hand.push(...game.pile);
    loser.hand.sort(byRankThenSuit);
    game.result = {
        caller: pid, accused: lp.by, bluff: !truthful, cards: lp.cards.slice(),
        rankIndex: lp.rankIndex, loser: loserPid, picked
    };
    game.pile = [];
    game.lastPlay = null;
    game.lock = null;
    game.roundOver = false;

    if (game.pendingWin !== null && truthful) {
        finish(game.pendingWin);                        // honest last play: they're out
    } else {
        game.pendingWin = null;
        game.starter = starterPid;
        game.turn = starterPid;
    }
    return { ok: true };
}

function playAgain() {
    if (game.phase !== "over") return;
    game.players = game.players.filter((p) => !p.out);
    if (game.players.length < RULES.minPlayers) {
        game.phase = "lobby";
        game.players.forEach((p) => { p.hand = []; });
        Object.assign(game, { result: null, pile: [], lastPlay: null, winner: null, lock: null, roundOver: false, log: [] });
    } else {
        dealGame();
    }
}

function removePlayer(pid) {
    conns.delete(pid);
    if (!game) return;

    if (game.phase === "lobby") {
        game.players = game.players.filter((p) => p.pid !== pid);
        broadcast();
        return;
    }

    const p = seat(pid);
    if (!p || p.out) return;
    p.out = true;
    p.hand = [];

    if (game.phase === "playing") {
        if (game.lastPlay && game.lastPlay.by === pid) game.lastPlay = null;
        if (game.pendingWin === pid) game.pendingWin = null;

        const alive = activePlayers();
        if (alive.length < RULES.minPlayers) {
            finish(alive.length === 1 ? alive[0].pid : null, "left");
        } else if (game.starter === pid) {
            // The leader left: the next player leads a fresh round and the old pile burns.
            game.starter = nextActive(pid);
            game.turn = game.starter;
            game.lock = null;
            game.roundOver = false;
            game.lastPlay = null;
            burnPile();
        } else if (game.turn === pid) {
            advanceFrom(pid);
        }
    }
    broadcast();
}

/* What a given player is allowed to know. Other hands never leave the host. */
function viewFor(pid) {
    const me = seat(pid);
    const lp = game.lastPlay;
    return {
        phase: game.phase,
        you: pid,
        code: roomCode,
        players: game.players.map((p) => ({ pid: p.pid, name: p.name, count: p.hand.length, out: p.out })),
        hand: me && !me.out ? me.hand.slice() : [],
        turn: game.turn,
        starter: game.starter,
        lock: game.lock,
        roundOver: game.roundOver,
        pileCount: game.pile.length,
        lastPlay: lp ? { by: lp.by, count: lp.cards.length, rankIndex: lp.rankIndex } : null,
        pendingWin: game.pendingWin,
        result: game.result,
        winner: game.winner,
        endReason: game.endReason,
        log: game.log.slice(-4)
    };
}

function broadcast() {
    view = viewFor(0);
    render();
    conns.forEach((c, pid) => {
        if (c.open) c.send({ type: "state", view: viewFor(pid) });
    });
}

/* =====================================================================
   VIEW HELPERS
   ===================================================================== */
function show(id) {
    VIEWS.forEach((v) => { $(v).hidden = v !== id; });
    shown = id;
    const el = $(id).querySelector("input") || $(id).querySelector("h2");
    if (el) el.focus();
}

function el(tag, className, text) {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = text;
    return node;
}

function nameOf(pid) {
    const p = view && view.players.find((x) => x.pid === pid);
    return p ? p.name : "Someone";
}
const who = (pid) => (view && pid === view.you ? "You" : nameOf(pid));
const whoObj = (pid) => (view && pid === view.you ? "you" : nameOf(pid));
const verb = (pid, you, they) => (view && pid === view.you ? you : they);
function plural(n, word) { return `${n} ${word}${n === 1 ? "" : "s"}`; }

function cardLabel(id) { return `${RANK_SINGULAR[cardRank(id)]} of ${SUIT_NAMES[cardSuit(id)]}`; }

function cardEl(id, kind, extra) {
    const node = el(kind === "button" ? "button" : "span", "card" + (RED_SUIT[cardSuit(id)] ? " red" : "") + (extra ? " " + extra : ""));
    if (kind === "button") node.type = "button";
    node.append(el("span", "c-rank", RANKS[cardRank(id)]), el("span", "c-suit", SUITS[cardSuit(id)] + "︎"));
    node.setAttribute(kind === "button" ? "aria-label" : "title", cardLabel(id));
    return node;
}

/* Which controls does this player have right now? */
function modeOf(v) {
    const playing = v.phase === "playing";
    const myTurn = playing && v.turn === v.you;
    const letStand = myTurn && v.pendingWin !== null;
    const declaring = myTurn && !letStand && (v.lock === null || v.roundOver);
    const following = myTurn && !letStand && !declaring;
    const canCall = playing && v.lastPlay !== null && v.lastPlay.by !== v.you;
    return { playing, myTurn, letStand, declaring, following, canCall };
}

/* =====================================================================
   RENDERING
   ===================================================================== */
function render() {
    if (!view) return;
    const target = view.phase === "lobby" ? "roomView" : "gameView";
    if (shown !== target) show(target);
    if (target === "roomView") renderRoom(); else renderGame();
}

function renderRoom() {
    const v = view;
    const isHost = role === "host";
    $("partyCode").textContent = v.code || "…";
    $("copyBtn").disabled = !v.code;
    $("roomHeading").textContent = isHost ? "Your room" : "Waiting room";
    $("roomHint").textContent = isHost
        ? "Share this code. Friends enter it on their own device."
        : "You're in. The host will start the game.";

    $("rosterCount").textContent = `${v.players.length} of ${RULES.maxPlayers}`;
    const list = $("roster");
    list.innerHTML = "";
    v.players.forEach((p) => {
        const li = el("li", "roster-row");
        li.append(el("span", "roster-name", p.name));
        const tags = [];
        if (p.pid === 0) tags.push("Host");
        if (p.pid === v.you) tags.push("You");
        if (tags.length) li.append(el("span", "roster-tag", tags.join(" · ")));
        list.appendChild(li);
    });

    const enough = v.players.length >= RULES.minPlayers;
    $("startBtn").hidden = !isHost;
    $("startBtn").disabled = !enough;
    $("roomStatus").textContent = isHost
        ? (enough ? `Ready to start with ${v.players.length} players.` : "Waiting for at least one more player…")
        : "Waiting for the host to start the game…";
}

function statusText(v, m) {
    if (v.phase === "over") {
        if (v.endReason === "left" && v.winner === null) return "Everyone left";
        return v.winner === v.you ? "You win" : `${nameOf(v.winner)} wins`;
    }
    if (m.letStand) return `${nameOf(v.pendingWin)} played their last cards`;
    if (m.declaring) return v.roundOver ? "Round complete. You lead again" : "You lead the round";
    if (m.myTurn) return `Your turn: play ${RANK_NAMES[v.lock.rankIndex]} or pass`;
    if (v.roundOver) return `Round complete. ${nameOf(v.starter)} leads next`;
    return `${nameOf(v.turn)}’s turn`;
}

function feedLine(e) {
    if (e.t === "play") {
        return e.starts
            ? `${who(e.by)} ${verb(e.by, "lead", "leads")} with ${e.count} × ${RANK_NAMES[e.rank]}`
            : `${who(e.by)} played ${plural(e.count, "card")} as ${RANK_NAMES[e.rank]}`;
    }
    if (e.t === "pass") return `${who(e.by)} passed`;
    if (e.t === "burn") return `${plural(e.count, "card")} burned`;
    return "";
}

function renderGame() {
    const v = view;
    const m = modeOf(v);
    const over = v.phase === "over";

    $("roomLine").textContent = `Room ${v.code}`;
    $("statusLine").textContent = statusText(v, m);

    // seats
    const seats = $("seats");
    seats.innerHTML = "";
    v.players.forEach((p) => {
        const li = el("li", "seat" + (!over && p.pid === v.turn ? " turn" : "") + (p.out ? " gone" : ""));
        li.append(el("span", "seat-name", p.name + (p.pid === v.you ? " (you)" : "")));
        const meta = el("span", "seat-meta");
        if (!over && !p.out && p.pid === v.starter) meta.append(el("span", "seat-tag", "Leads"));
        meta.append(el("span", "seat-count", p.out ? "Left" : plural(p.count, "card")));
        li.append(meta);
        if (!over && p.pid === v.turn) li.setAttribute("aria-current", "true");
        seats.appendChild(li);
    });

    // table
    $("pileCount").textContent = plural(v.pileCount, "card");
    const art = $("pileArt");
    art.innerHTML = "";
    for (let i = 0; i < Math.min(3, v.pileCount); i++) art.appendChild(el("span", "card back xs"));
    if (v.lock && !v.roundOver) {
        $("claimRank").textContent = RANKS[v.lock.rankIndex];
        $("claimName").textContent = RANK_NAMES[v.lock.rankIndex];
    } else if (v.lock && v.roundOver) {
        $("claimRank").textContent = "Done";
        $("claimName").textContent = "Round complete";
    } else {
        $("claimRank").textContent = "Open";
        $("claimName").textContent = "Leader picks";
    }
    $("table").hidden = over;

    // recent moves
    const feed = $("feed");
    feed.innerHTML = "";
    if (!over) v.log.forEach((e) => { const t = feedLine(e); if (t) feed.appendChild(el("li", "", t)); });

    const last = $("lastPlay");
    if (over) {
        last.textContent = role === "host" ? "" : "Waiting for the host to start another game.";
        if (v.endReason === "left" && v.winner !== null) last.textContent = "Everyone else left the room.";
    } else if (v.roundOver && v.lastPlay && v.lastPlay.by !== v.you) {
        last.textContent = "Last chance to call bluff before the pile burns.";
    } else {
        last.textContent = "";
    }

    renderResult();
    renderDeclare(m);
    renderHand();
    renderActions(m);
}

function renderResult() {
    const v = view;
    const r = v.result;
    const over = v.phase === "over";
    const box = $("resultBox");

    const cards = $("resultCards");
    cards.innerHTML = "";

    const headline = r && `${who(r.caller)} called bluff on ${whoObj(r.accused)}`;
    const outcome = r && `${who(r.accused)} ${verb(r.accused, "were", "was")} ${r.bluff ? "bluffing" : "telling the truth"}`;

    if (r) {
        r.cards.forEach((id) => {
            cards.appendChild(cardEl(id, "span", "sm" + (cardRank(id) === r.rankIndex ? "" : " miss")));
        });
        cards.setAttribute("aria-label", `Claimed ${RANK_NAMES[r.rankIndex]}`);
    }

    if (over && v.winner !== null) {
        // Final screen: the winner first, then how the last challenge went (if there was one).
        box.hidden = false;
        $("resultLabel").textContent = "Winner";
        $("resultTitle").textContent = nameOf(v.winner);
        $("resultDetail").textContent = r ? `${headline}. ${outcome}.` : "First to play every card.";
        return;
    }
    if (!r) { box.hidden = true; return; }

    box.hidden = false;
    $("resultLabel").textContent = headline;
    $("resultTitle").textContent = outcome;

    let detail = `${who(r.loser)} ${verb(r.loser, "pick", "picks")} up the pile (${plural(r.picked, "card")}).`;
    if (v.phase === "playing") detail += ` ${who(v.starter)} ${verb(v.starter, "lead", "leads")} the next round.`;
    $("resultDetail").textContent = detail;
}

function renderDeclare(m) {
    const box = $("declare");
    box.hidden = !m.declaring;
    if (!m.declaring) { declRank = null; return; }
    [...$("rankPick").children].forEach((b) => {
        b.setAttribute("aria-checked", Number(b.dataset.rank) === declRank ? "true" : "false");
    });
}

function renderHand() {
    const v = view;
    const hand = $("hand");
    const key = v.hand.join(",");

    for (const id of [...selected]) if (!v.hand.includes(id)) selected.delete(id);

    if (key !== handKey) {
        handKey = key;
        hand.innerHTML = "";
        v.hand.forEach((id) => {
            const b = cardEl(id, "button");
            b.dataset.id = id;
            b.addEventListener("click", () => toggleCard(id));
            hand.appendChild(b);
        });
    }
    [...hand.children].forEach((b) => {
        const on = selected.has(Number(b.dataset.id));
        b.classList.toggle("selected", on);
        b.setAttribute("aria-pressed", on ? "true" : "false");
    });

    $("handLabel").textContent = v.phase === "over" ? "Your hand" : `Your hand · ${plural(v.hand.length, "card")}`;
    $("hand").hidden = v.hand.length === 0;
    $("handLabel").hidden = v.hand.length === 0 && v.phase === "over";
}

function renderActions(m) {
    const v = view;
    const over = v.phase === "over";
    const n = selected.size;
    const isHost = role === "host";

    $("callBtn").hidden = over;
    $("passBtn").hidden = over || m.declaring;
    $("playBtn").hidden = over || m.letStand;
    $("againBtn").hidden = !(over && isHost);
    $("gameActions").hidden = over && !isHost;

    $("callBtn").disabled = !m.canCall;
    $("passBtn").textContent = m.letStand ? "Let it stand" : "Pass";
    $("passBtn").disabled = !(m.following || m.letStand);

    let label = "Play cards";
    let ready = false;
    if (m.declaring) {
        ready = n > 0 && declRank !== null;
        if (n > 0 && declRank !== null) label = `Play ${plural(n, "card")} as ${RANK_NAMES[declRank]}`;
        else if (n > 0) label = "Choose a rank";
    } else if (m.following) {
        ready = n > 0;
        if (n > 0) label = `Play ${plural(n, "card")} as ${RANK_NAMES[v.lock.rankIndex]}`;
    }
    $("playBtn").disabled = !ready;
    $("playBtn").textContent = label;
}

/* =====================================================================
   PLAYER ACTIONS
   ===================================================================== */
function setPlayError(message) { $("playError").textContent = message || ""; }

function selectionCap() {
    return RULES.maxCards || Infinity;
}

function toggleCard(id) {
    setPlayError("");
    if (selected.has(id)) {
        selected.delete(id);
    } else {
        const cap = selectionCap();
        if (selected.size >= cap) {
            setPlayError(`You can play up to ${cap} cards at once.`);
            return;
        }
        selected.add(id);
        if (declRank === null && view && modeOf(view).declaring) declRank = cardRank(id);
    }
    if (view) { const m = modeOf(view); renderDeclare(m); renderHand(); renderActions(m); }
}

function act(type, payload) {
    setPlayError("");
    if (role === "host") {
        let res;
        if (type === "play") res = applyPlay(0, payload.cards, payload.rankIndex);
        else if (type === "pass") res = applyPass(0);
        else if (type === "call") res = applyCall(0);
        if (!res || !res.ok) { setPlayError(res ? res.error : ""); return false; }
        broadcast();
        return true;
    }
    if (conn && conn.open) conn.send(Object.assign({ type }, payload));
    return true;
}

$("playBtn").addEventListener("click", () => {
    const cards = [...selected];
    if (!cards.length) return;
    const rankIndex = view && modeOf(view).declaring ? declRank : undefined;
    // The selection is kept until the new state arrives (cards that left the hand are pruned
    // then), so a rejected play such as "hold on" doesn't lose it.
    act("play", { cards, rankIndex });
    if (view) { const m = modeOf(view); renderDeclare(m); renderHand(); renderActions(m); }
});
$("callBtn").addEventListener("click", () => act("call"));
$("passBtn").addEventListener("click", () => act("pass"));

// Rank picker (built once)
RANKS.forEach((label, i) => {
    const b = el("button", "rank-btn", label);
    b.type = "button";
    b.dataset.rank = i;
    b.setAttribute("role", "radio");
    b.setAttribute("aria-checked", "false");
    b.setAttribute("aria-label", RANK_NAMES[i]);
    b.addEventListener("click", () => {
        declRank = i;
        setPlayError("");
        if (view) { const m = modeOf(view); renderDeclare(m); renderActions(m); }
    });
    $("rankPick").appendChild(b);
});

$("againBtn").addEventListener("click", () => {
    if (role !== "host" || !game) return;
    selected.clear();
    declRank = null;
    playAgain();
    broadcast();
});

$("startBtn").addEventListener("click", () => {
    if (role !== "host" || !game || game.phase !== "lobby") return;
    if (activePlayers().length < RULES.minPlayers) return;
    selected.clear();
    declRank = null;
    dealGame();
    broadcast();
});

/* =====================================================================
   CONNECTIONS
   ===================================================================== */
function teardown() {
    // Clear state first so close events fired by the calls below see "we left on purpose".
    const guestConn = conn, hostConns = [...conns.values()], p = peer;
    conn = null; peer = null; role = null; game = null; view = null; shown = null;
    conns.clear();
    nextPid = 1; hostAttempts = 0; roomCode = ""; handKey = ""; declRank = null;
    selected.clear();

    if (guestConn) { try { guestConn.close(); } catch (e) {} }
    hostConns.forEach((c) => { try { c.close(); } catch (e) {} });
    if (p) { try { p.destroy(); } catch (e) {} }
}

function backToLobby(message) {
    teardown();
    $("lobbyError").textContent = message || "";
    $("joinError").textContent = "";
    $("codeInput").value = "";
    setPlayError("");
    show("lobby");
}

function peerLibMissing() {
    if (typeof Peer !== "undefined") return false;
    $("lobbyError").textContent = "Couldn't load the online connection library. Check your internet and reload.";
    return true;
}

function readName() {
    const name = $("nameInput").value.replace(/\s+/g, " ").trim();
    if (!name) {
        $("lobbyError").textContent = "Enter your name first.";
        $("nameInput").setAttribute("aria-invalid", "true");
        $("nameInput").focus();
        return null;
    }
    $("nameInput").removeAttribute("aria-invalid");
    $("lobbyError").textContent = "";
    return name;
}

/* ---------- host ---------- */
function startHosting() {
    const name = readName();
    if (name === null || peerLibMissing()) return;
    myName = name;
    role = "host";
    game = newGame();
    roomCode = "";
    view = null;
    $("partyCode").textContent = "…";
    $("roster").innerHTML = "";
    $("roomStatus").textContent = "Creating room…";
    $("copyBtn").disabled = true;
    $("startBtn").hidden = true;
    show("roomView");
    openHostPeer();
}

function openHostPeer() {
    const code = makeCode();
    const p = new Peer(PREFIX + code);
    peer = p;

    p.on("open", () => {
        roomCode = code;
        addPlayer(0, myName);
        broadcast();
    });

    p.on("connection", (c) => {
        c.on("data", (msg) => onHostMessage(c, msg));
        c.on("close", () => onGuestGone(c));
        c.on("error", () => onGuestGone(c));
    });

    p.on("disconnected", () => { try { p.reconnect(); } catch (e) {} });

    p.on("error", (err) => {
        if (err.type === "unavailable-id" && hostAttempts < 5) {
            hostAttempts++;
            try { p.destroy(); } catch (e) {}
            openHostPeer();
        } else if (peer === p) {
            backToLobby("Couldn't create a room. Check your connection and try again.");
        }
    });
}

function onGuestGone(c) {
    if (!peer || c.bluffPid === undefined) return;
    const pid = c.bluffPid;
    c.bluffPid = undefined;
    removePlayer(pid);
}

function reject(c, reason) {
    try { c.send({ type: "rejected", reason }); } catch (e) {}
    setTimeout(() => { try { c.close(); } catch (e) {} }, 300);
}

function onHostMessage(c, msg) {
    if (!game || !msg || typeof msg !== "object") return;

    if (msg.type === "join") {
        if (c.bluffPid !== undefined) return;
        if (game.phase !== "lobby") return reject(c, "That game has already started.");
        if (activePlayers().length >= RULES.maxPlayers) return reject(c, "That room is full.");
        const pid = nextPid++;
        c.bluffPid = pid;
        conns.set(pid, c);
        addPlayer(pid, msg.name);
        broadcast();
        return;
    }

    const pid = c.bluffPid;
    if (pid === undefined) return;

    let res = null;
    if (msg.type === "play") res = applyPlay(pid, msg.cards, msg.rankIndex);
    else if (msg.type === "pass") res = applyPass(pid);
    else if (msg.type === "call") res = applyCall(pid);
    else return;

    if (res.ok) broadcast();
    else if (c.open) c.send({ type: "error", message: res.error });
}

/* ---------- guest ---------- */
function joinRoom(code) {
    const name = readName();
    if (name === null) { show("lobby"); return; }
    if (peerLibMissing()) { show("lobby"); return; }

    myName = name;
    const btn = $("joinSubmit");
    btn.disabled = true;
    $("joinError").textContent = "";

    const p = new Peer();
    peer = p;
    role = "guest";
    let settled = false;

    const fail = (msg) => {
        if (settled) return;
        settled = true;
        btn.disabled = false;
        teardown();
        $("joinError").textContent = msg;
        $("codeInput").setAttribute("aria-invalid", "true");
        show("joinView");
    };

    const timeout = setTimeout(() => fail("Couldn't reach that room. Check the code and try again."), 12000);

    p.on("open", () => {
        const c = p.connect(PREFIX + code, { reliable: true });
        c.on("open", () => {
            if (settled) return;
            settled = true;
            clearTimeout(timeout);
            btn.disabled = false;
            wireGuest(c);
            c.send({ type: "join", name: myName });
        });
    });

    p.on("error", (err) => {
        clearTimeout(timeout);
        if (err.type === "peer-unavailable") fail("No room found with that code.");
        else if (settled) backToLobby("The connection was lost.");
        else fail("Couldn't connect. Check your internet and try again.");
    });
}

function wireGuest(c) {
    conn = c;
    c.on("data", (msg) => {
        if (!msg || typeof msg !== "object") return;
        if (msg.type === "state" && msg.view) {
            view = msg.view;
            render();
        } else if (msg.type === "rejected") {
            backToLobby(msg.reason || "Couldn't join that room.");
        } else if (msg.type === "error") {
            setPlayError(msg.message);
        }
    });
    c.on("close", () => {
        if (!peer) return; // we left on purpose
        backToLobby("The host closed the room.");
    });
    c.on("error", () => backToLobby("The connection was lost."));
}

/* =====================================================================
   PAGE EVENTS
   ===================================================================== */
$("hostBtn").addEventListener("click", startHosting);

$("joinBtn").addEventListener("click", () => {
    if (readName() === null) return;
    $("joinError").textContent = "";
    $("codeInput").removeAttribute("aria-invalid");
    show("joinView");
});

document.querySelectorAll("[data-leave]").forEach((b) =>
    b.addEventListener("click", () => backToLobby("")));

$("homeLink").addEventListener("click", () => teardown());
window.addEventListener("pagehide", () => teardown());

$("nameInput").addEventListener("input", () => $("nameInput").removeAttribute("aria-invalid"));

$("codeInput").addEventListener("input", (e) => {
    e.target.value = e.target.value.toUpperCase().replace(/[^A-Z0-9]/g, "");
    e.target.removeAttribute("aria-invalid");
});

$("joinForm").addEventListener("submit", (e) => {
    e.preventDefault();
    const code = $("codeInput").value.trim().toUpperCase();
    if (code.length !== CODE_LENGTH) {
        $("joinError").textContent = `Enter the ${CODE_LENGTH}-character code from the host.`;
        $("codeInput").setAttribute("aria-invalid", "true");
        $("codeInput").focus();
        return;
    }
    joinRoom(code);
});

$("copyBtn").addEventListener("click", async () => {
    const code = $("partyCode").textContent;
    try {
        await navigator.clipboard.writeText(code);
        $("copyBtn").textContent = "Copied";
    } catch (e) {
        $("copyBtn").textContent = "Select the code to copy";
    }
    setTimeout(() => { $("copyBtn").textContent = "Copy code"; }, 1800);
});
