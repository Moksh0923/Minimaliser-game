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
   applyCall.

   ANIMATION: the host stamps every action with a numbered event (deal, play, pass, call,
   burn). Every device receives the latest few events inside its view, and plays each one it
   hasn't seen yet. Animations are purely cosmetic; the table underneath is always drawn
   straight from the state.

   CARD LOOK: cards are drawn like a classic playing-card deck (see cardEl and PIPS). */

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
let eventN = 0;             // host only: numbers every event, never reset

let view = null;            // what this device is allowed to see
let lastView = null;        // the view before this one (to spot changes)
let shown = null;
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
        log: [],
        events: []            // numbered moves for the animations
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

// Animation cues. Only public facts go in here (a call reveals its cards anyway).
function pushEvent(entry) {
    entry.n = ++eventN;
    game.events.push(entry);
    if (game.events.length > 8) game.events.shift();
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
    if (game.pile.length) {
        note({ t: "burn", count: game.pile.length });
        pushEvent({ t: "burn", count: game.pile.length });
    }
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
        winner: null, endReason: "", lock: null, roundOver: false, log: [], events: [],
        starter, turn: starter
    });
    pushEvent({ t: "deal" });
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
    pushEvent({ t: "play", by: pid, count: cards.length, rank: game.lock.rankIndex, starts: declaring });
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
    pushEvent({ t: "pass", by: pid });
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
    pushEvent({
        t: "call", caller: pid, accused: lp.by, bluff: !truthful, cards: lp.cards.slice(),
        rankIndex: lp.rankIndex, loser: loserPid, picked
    });
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
        Object.assign(game, { result: null, pile: [], lastPlay: null, winner: null, lock: null, roundOver: false, log: [], events: [] });
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
        sinceMs: lp ? Date.now() - game.playAt : null,   // how long ago, so every device can draw the call timer
        windowMs: RULES.callWindowMs,
        pendingWin: game.pendingWin,
        result: game.result,
        winner: game.winner,
        endReason: game.endReason,
        log: game.log.slice(-4),
        events: game.events.slice(-6)
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
    document.body.classList.toggle("in-game", id === "gameView");
    shown = id;
    const el = $(id).querySelector("input") || $(id).querySelector("h2");
    if (el) el.focus({ preventScroll: true });
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

/* ---------- the deck: classic playing-card faces ----------
   Pip positions are [x, y] inside the pip field, where x is 0 (left) / 0.5 / 1 (right)
   and y runs 0 (top) to 1 (bottom). Pips in the lower half are turned upside down, exactly
   like a printed deck. Index 0 is the Ace, 1 is the Two ... 9 is the Ten. */
const PIPS = [
    [[0.5, 0.5]],                                                                       // A (drawn large)
    [[0.5, 0], [0.5, 1]],                                                               // 2
    [[0.5, 0], [0.5, 0.5], [0.5, 1]],                                                   // 3
    [[0, 0], [1, 0], [0, 1], [1, 1]],                                                   // 4
    [[0, 0], [1, 0], [0.5, 0.5], [0, 1], [1, 1]],                                       // 5
    [[0, 0], [1, 0], [0, 0.5], [1, 0.5], [0, 1], [1, 1]],                               // 6
    [[0, 0], [1, 0], [0.5, 0.25], [0, 0.5], [1, 0.5], [0, 1], [1, 1]],                  // 7
    [[0, 0], [1, 0], [0.5, 0.25], [0, 0.5], [1, 0.5], [0.5, 0.75], [0, 1], [1, 1]],     // 8
    [[0, 0], [1, 0], [0, 0.333], [1, 0.333], [0.5, 0.5], [0, 0.667], [1, 0.667], [0, 1], [1, 1]],   // 9
    [[0, 0], [1, 0], [0.5, 0.1667], [0, 0.333], [1, 0.333], [0, 0.667], [1, 0.667], [0.5, 0.8333], [0, 1], [1, 1]]  // 10
];

function cardEl(id, kind, extra) {
    const rank = cardRank(id);
    const suitChar = SUITS[cardSuit(id)] + "︎";      // text (not emoji) presentation
    const node = el(kind === "button" ? "button" : "span", `card s${cardSuit(id)}` + (extra ? " " + extra : ""));
    if (kind === "button") node.type = "button";

    // rank and suit in opposite corners
    const corner = (cls) => {
        const c = el("span", "c-corner" + (cls ? " " + cls : ""));
        c.append(el("span", "c-rank", RANKS[rank]), el("span", "c-suit", suitChar));
        return c;
    };
    node.append(corner(""), corner("br"));

    if (rank >= 10) {                                   // J, Q, K: framed court panel
        const face = el("span", "c-face");
        face.append(
                el("span", "c-face-suit", suitChar),
                el("span", "c-face-letter", RANKS[rank]),
                el("span", "c-face-suit br", suitChar)
        );
        node.appendChild(face);
    } else {                                            // A to 10: pips
        const field = el("span", "c-pips");
        PIPS[rank].forEach(([x, y]) => {
            const p = el("span", "pip" + (rank === 0 ? " ace" : "") + (y > 0.5 ? " down" : ""), suitChar);
            p.style.left = `${x * 100}%`;
            p.style.top = `${y * 100}%`;
            field.appendChild(p);
        });
        node.appendChild(field);
    }

    node.setAttribute(kind === "button" ? "aria-label" : "title", cardLabel(id));
    return node;
}

function paintAvatar(node, name) {
    let h = 0;
    for (const ch of name) h = (h * 31 + ch.charCodeAt(0)) % 360;
    node.textContent = (name.trim()[0] || "?").toUpperCase();
    node.style.setProperty("--hue", h);
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
const seatEls = new Map();      // pid -> { root, fan, av, count, tag, pos, cap }
let seatKey = "";
const handEls = new Map();      // card id -> button (kept between renders so cards can animate)
let seenEvent = null;           // highest event number already played on this device
const fxHold = { pile: null, caption: false, over: false };   // parts of the table held back until an animation finishes
let cdKey = null;               // which play the call-timer bar is running for
let overShown = false;

function render() {
    if (!view) return;
    const target = view.phase === "lobby" ? "roomView" : "gameView";
    if (shown !== target) show(target);
    if (target === "roomView") {
        if (seenEvent === null) seenEvent = 0;
        renderRoom();
    } else {
        renderGame();
    }
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
    const old = lastView;
    const m = modeOf(v);
    const over = v.phase === "over";

    // What happened since we last drew? (Looked at before the DOM changes, because the
    // animations start from where things were.)
    const events = freshEvents(v);
    const animate = events.length > 0 && !reduceMotion();
    const snap = animate ? snapshotFx(events) : null;
    if (animate) {
        const calls = events.some((e) => e.t === "call");
        if (old && (calls || events.some((e) => e.t === "burn"))) fxHold.pile = old.pileCount;
        if (calls) { fxHold.caption = true; if (over) fxHold.over = true; }
    }
    if (events.some((e) => e.t === "deal")) {          // a fresh deal: start the hand from scratch
        handEls.clear();
        $("handIn").innerHTML = "";
        overShown = false;
    }

    $("roomLine").textContent = `Room ${v.code}`;
    const status = $("statusLine");
    status.textContent = statusText(v, m);
    status.classList.toggle("mine", m.myTurn && !over);

    renderSeats(v, over);
    renderPile(fxHold.pile !== null ? fxHold.pile : v.pileCount);
    renderClaim(v);

    const feed = $("feed");
    feed.innerHTML = "";
    if (!over) v.log.forEach((e) => { const t = feedLine(e); if (t) feed.appendChild(el("li", "", t)); });

    const last = $("lastPlay");
    last.textContent = !over && v.roundOver && v.lastPlay && v.lastPlay.by !== v.you
            ? "Last chance to call bluff before the pile burns."
            : "";

    renderCaption(v);
    renderDeclare(m);
    const fresh = renderHand();
    renderMe(v, over);
    renderActions(m);
    renderOver(v);

    if (animate) {
        if (events.some((e) => e.t === "call" && e.loser === v.you)) {
            fresh.forEach((n) => { n.style.visibility = "hidden"; });   // they arrive with the pickup
        }
        queueFx(events, snap, fresh, v);
    }

    if (old && !over && v.phase === "playing" && v.turn === v.you && old.turn !== v.you) buzz();
    lastView = v;
}

/* ---------- seats around the table ---------- */
function layoutSlots(opps) {
    const n = opps.length;
    const out = { left: [], top: [], right: [] };
    if (n === 1) { out.top = opps.slice(); return out; }
    if (n === 2) { out.left = [opps[0]]; out.right = [opps[1]]; return out; }
    const side = n >= 6 ? 2 : 1;
    // Clockwise from you: up the left edge, across the top, down the right edge.
    out.left = opps.slice(0, side);
    out.top = opps.slice(side, n - side);
    out.right = opps.slice(n - side);
    return out;
}

function buildSeat(p, pos, cap) {
    const root = el("div", `opp opp-${pos}`);
    root.setAttribute("role", "group");
    const fan = el("div", "fan");
    const av = el("span", "avatar");
    paintAvatar(av, p.name);
    const count = el("span", "opp-count", "0");
    const row = el("div", "opp-row");
    row.append(av, count);
    const name = el("span", "opp-name", p.name);
    const tag = el("span", "opp-tag", "Leads");
    const info = el("div", "opp-info");
    info.append(name, row, tag);
    if (pos === "top") root.append(fan, info); else root.append(info, fan);
    return { root, fan, av, count, tag, pos, cap };
}

function buildSeats(v) {
    ["oppTop", "oppLeft", "oppRight"].forEach((id) => { $(id).innerHTML = ""; });
    seatEls.clear();
    const n = v.players.length;
    const meIdx = Math.max(0, v.players.findIndex((p) => p.pid === v.you));
    const opps = [];
    for (let k = 1; k < n; k++) opps.push(v.players[(meIdx + k) % n]);

    const slots = layoutSlots(opps);
    const topCap = slots.top.length <= 1 ? 10 : slots.top.length === 2 ? 7 : slots.top.length === 3 ? 5 : 4;
    const sideCap = slots.left.length > 1 ? 5 : 9;
    const add = (p, pos, host, cap) => {
        const s = buildSeat(p, pos, cap);
        seatEls.set(p.pid, s);
        host.appendChild(s.root);
    };
    // The left edge is drawn top to bottom, so reverse it to keep the clockwise order.
    slots.left.slice().reverse().forEach((p) => add(p, "left", $("oppLeft"), sideCap));
    slots.top.forEach((p) => add(p, "top", $("oppTop"), topCap));
    slots.right.forEach((p) => add(p, "right", $("oppRight"), sideCap));
    $("oppTop").classList.toggle("many", slots.top.length > 1);
    $("tv").classList.toggle("crowded", slots.top.length > 1);   // no room for the room-code chip
}

function renderSeats(v, over) {
    const key = v.players.map((p) => p.pid).join(",") + "|" + v.you;
    if (key !== seatKey) { seatKey = key; buildSeats(v); }

    v.players.forEach((p) => {
        const s = seatEls.get(p.pid);
        if (!s) return;
        const turn = !over && p.pid === v.turn;
        s.root.classList.toggle("turn", turn);
        s.root.classList.toggle("gone", p.out);
        s.root.setAttribute("aria-label", `${p.name}, ${p.out ? "left the game" : plural(p.count, "card")}`);
        if (turn) s.root.setAttribute("aria-current", "true"); else s.root.removeAttribute("aria-current");
        s.count.textContent = p.out ? "–" : p.count;
        s.tag.hidden = !(!over && !p.out && p.pid === v.starter);

        const want = p.out ? 0 : Math.min(p.count, s.cap);
        while (s.fan.children.length < want) s.fan.appendChild(el("span", "card back"));
        while (s.fan.children.length > want) s.fan.lastChild.remove();
    });
}

function renderMe(v, over) {
    const name = nameOf(v.you);
    paintAvatar($("meAvatar"), name);
    $("meName").textContent = name;
    $("me").classList.toggle("turn", !over && v.turn === v.you);
    $("handLabel").textContent = plural(v.hand.length, "card");
}

/* ---------- pile and claim ---------- */
const JITTER = [[0, 0, 0], [3, -2, -5], [-4, 2, 6], [2, 3, -3], [-3, -3, 4], [4, 0, 7], [-2, 4, -6]];
const jit = (i) => { const j = JITTER[i % JITTER.length]; return { x: j[0], y: j[1], r: j[2] }; };

function renderPile(count) {
    const pile = $("pile");
    pile.innerHTML = "";
    for (let i = 0; i < Math.min(count, 7); i++) {
        const c = el("span", "card back");
        const j = jit(i);
        c.style.transform = `translate(${j.x}px, ${j.y}px) rotate(${j.r}deg)`;
        pile.appendChild(c);
    }
    pile.classList.toggle("empty", count === 0);
    $("pileCount").textContent = count ? plural(count, "card") : "Empty";
}

let claimKey = "";
function renderClaim(v) {
    const open = !(v.lock && !v.roundOver);
    let rank, name;
    if (v.lock && !v.roundOver) { rank = RANKS[v.lock.rankIndex]; name = RANK_NAMES[v.lock.rankIndex]; }
    else if (v.lock && v.roundOver) { rank = "✓"; name = "Round complete"; }
    else { rank = "?"; name = "Leader picks"; }
    $("claimRank").textContent = rank;
    $("claimName").textContent = name;
    $("claimCard").classList.toggle("dim", open);
    const key = rank + name;
    if (key !== claimKey) {
        claimKey = key;
        if (!open) {
            const c = $("claimCard");
            c.classList.remove("pop");
            void c.offsetWidth;
            c.classList.add("pop");
        }
    }
}

function renderCaption(v) {
    const r = v.result;
    const box = $("resultBox");
    const showIt = !!r && v.phase !== "over" && !fxHold.caption;
    box.hidden = !showIt;
    if (!showIt) return;
    $("resultTitle").textContent = `${who(r.caller)} called bluff on ${whoObj(r.accused)}`;
    $("resultDetail").textContent =
            `${who(r.accused)} ${verb(r.accused, "were", "was")} ${r.bluff ? "bluffing" : "telling the truth"}. ` +
            `${who(r.loser)} ${verb(r.loser, "pick", "picks")} up ${plural(r.picked, "card")}.`;
}

function renderOver(v) {
    const open = v.phase === "over" && !fxHold.over;
    $("overBox").hidden = !open;
    if (!open) { if (v.phase !== "over") overShown = false; return; }

    const r = v.result;
    const noWinner = v.winner === null;
    $("overLabel").textContent = noWinner ? "Game over" : "Winner";
    $("overTitle").textContent = noWinner ? "Everyone left" : (v.winner === v.you ? "You win" : nameOf(v.winner));

    let detail;
    if (v.endReason === "left" && !noWinner) detail = "Everyone else left the room.";
    else if (r && !noWinner) detail = `${who(r.caller)} called bluff on ${whoObj(r.accused)}. ${who(r.accused)} ${verb(r.accused, "were", "was")} ${r.bluff ? "bluffing" : "telling the truth"}.`;
    else detail = noWinner ? "" : "First to play every card.";
    if (role !== "host") detail += (detail ? " " : "") + "Waiting for the host to start another game.";
    $("overDetail").textContent = detail;
    $("againBtn").hidden = role !== "host";

    if (!overShown) {
        overShown = true;
        if (!noWinner && v.winner === v.you) confetti();
    }
}

function renderDeclare(m) {
    const box = $("declare");
    box.hidden = !m.declaring;
    if (!m.declaring) { declRank = null; return; }
    [...$("rankPick").children].forEach((b) => {
        b.setAttribute("aria-checked", Number(b.dataset.rank) === declRank ? "true" : "false");
    });
}

/* ---------- your hand ---------- */
function renderHand() {
    const v = view;
    const inner = $("handIn");
    const fresh = [];

    for (const id of [...selected]) if (!v.hand.includes(id)) selected.delete(id);

    const want = new Set(v.hand);
    for (const [id, node] of handEls) {
        if (!want.has(id)) { node.remove(); handEls.delete(id); }
    }

    // Keep existing card elements (so they can animate) and only add, remove and reorder.
    let cursor = inner.firstChild;
    v.hand.forEach((id) => {
        let node = handEls.get(id);
        if (!node) {
            node = cardEl(id, "button");
            node.dataset.id = id;
            node.addEventListener("click", () => toggleCard(id));
            handEls.set(id, node);
            fresh.push(node);
        }
        if (node === cursor) cursor = cursor.nextSibling;
        else inner.insertBefore(node, cursor);
    });

    [...inner.children].forEach((b) => {
        const on = selected.has(Number(b.dataset.id));
        b.classList.toggle("selected", on);
        b.setAttribute("aria-pressed", on ? "true" : "false");
    });

    fitHand();
    return fresh;
}

// Overlap the cards so a full hand fits the width; if it still can't, the hand scrolls.
function fitHand() {
    const scroller = $("hand");
    const inner = $("handIn");
    const n = inner.children.length;
    if (!n) return;
    const cw = inner.firstElementChild.offsetWidth;
    const avail = scroller.clientWidth - 24;
    const maxStep = cw * 0.64, minStep = cw * 0.42;
    let step = n > 1 ? (avail - cw) / (n - 1) : maxStep;
    step = Math.max(minStep, Math.min(maxStep, step));
    inner.style.setProperty("--ov", `${(cw - step).toFixed(1)}px`);
}

/* ---------- buttons ---------- */
function renderActions(m) {
    const v = view;
    const over = v.phase === "over";
    const n = selected.size;

    $("gameActions").hidden = over;
    $("callBtn").disabled = !m.canCall;
    $("passBtn").classList.toggle("is-off", m.declaring);
    $("passBtn").textContent = m.letStand ? "Let it stand" : "Pass";
    $("passBtn").disabled = !(m.following || m.letStand);
    $("playBtn").hidden = m.letStand;

    let label = "Play cards";
    let ready = false;
    if (!m.myTurn) {
        label = over ? "Play cards" : `Waiting for ${nameOf(v.turn)}…`;
    } else if (m.declaring) {
        ready = n > 0 && declRank !== null;
        if (n > 0 && declRank !== null) label = `Play ${plural(n, "card")} as ${RANK_NAMES[declRank]}`;
        else if (n > 0) label = "Choose a rank";
        else label = "Pick cards and a rank";
    } else if (m.following) {
        ready = n > 0;
        label = n > 0 ? `Play ${plural(n, "card")} as ${RANK_NAMES[v.lock.rankIndex]}` : `Pick cards to play as ${RANK_NAMES[v.lock.rankIndex]}`;
    }
    $("playBtn").disabled = !ready;
    $("playBtn").textContent = label;

    // The Call button drains while the next player is still being made to wait.
    const lastPlayEvent = (v.events || []).slice().reverse().find((e) => e.t === "play");
    if (v.lastPlay && v.sinceMs !== null && lastPlayEvent && lastPlayEvent.n !== cdKey) {
        cdKey = lastPlayEvent.n;
        const remain = v.windowMs - v.sinceMs;
        if (remain > 80) {
            const f = $("callFill");
            f.style.animation = "none";
            void f.offsetWidth;
            f.style.animation = `drain ${remain}ms linear forwards`;
        }
    }
}

/* =====================================================================
   ANIMATION
   Everything below is decoration. If any of it throws or is skipped, the game is still
   correct, because the table was already drawn from the state.
   ===================================================================== */
const EASE_OUT = "cubic-bezier(.2,.8,.2,1)";
const EASE_IN = "cubic-bezier(.5,0,.85,.4)";
const CANCEL = new Error("animation cancelled");

let fxTok = 0;                  // bumped when leaving a room, to stop animations in flight
let fxChain = Promise.resolve();
let fxPending = 0;

const reduceMotion = () => !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
const rectOf = (n) => n.getBoundingClientRect();
const centerOf = (r) => ({ x: r.left + r.width / 2, y: r.top + r.height / 2 });
const layer = () => $("fx");

function pause(ms, tok) {
    return new Promise((r) => setTimeout(r, ms)).then(() => { if (tok !== fxTok) throw CANCEL; });
}
async function settle(jobs, tok) {
    await Promise.all(jobs);
    if (tok !== fxTok) throw CANCEL;
}

function buzz() {
    try { if (navigator.vibrate) navigator.vibrate(25); } catch (e) {}
}

function freshEvents(v) {
    const evs = v.events || [];
    if (seenEvent === null) {                           // joined mid-game: don't replay history
        seenEvent = evs.length ? evs[evs.length - 1].n : 0;
        return [];
    }
    const fresh = evs.filter((e) => e.n > seenEvent);
    if (fresh.length) seenEvent = fresh[fresh.length - 1].n;
    return fresh;
}

// The cards you just played fly from where they sat in your hand, so note that first.
function snapshotFx(events) {
    const snap = { mine: null };
    if (events.some((e) => e.t === "play" && e.by === view.you)) {
        snap.mine = [...$("handIn").children]
                .filter((n) => selected.has(Number(n.dataset.id)))
                .map((n) => ({ id: Number(n.dataset.id), rect: rectOf(n) }));
    }
    return snap;
}

function queueFx(events, snap, fresh, v) {
    fxPending++;
    const tok = fxTok;
    fxChain = fxChain.then(async () => {
        try {
            for (const e of events) {
                if (tok !== fxTok) return;
                if (e.t === "deal") await fxDeal(fresh, tok);
                else if (e.t === "play") await fxPlay(e, v, snap, tok);
                else if (e.t === "pass") await fxPass(e, tok);
                else if (e.t === "burn") await fxBurn(e, tok);
                else if (e.t === "call") await fxCall(e, v, fresh, tok);
            }
        } catch (err) {
            /* cancelled, or an animation hiccup: carry on */
        } finally {
            if (tok === fxTok) {
                fresh.forEach((n) => { n.style.visibility = ""; });
                fxPending--;
                if (fxPending === 0) releaseHolds();
            }
        }
    });
}

function releaseHolds() {
    fxHold.pile = null; fxHold.caption = false; fxHold.over = false;
    if (shown !== "gameView" || !view) return;
    renderPile(view.pileCount);
    renderCaption(view);
    renderOver(view);
}

function resetFx() {
    fxTok++;
    fxChain = Promise.resolve();
    fxPending = 0;
    fxHold.pile = null; fxHold.caption = false; fxHold.over = false;
    $("fx").innerHTML = "";
    $("stage").hidden = true;
    $("stageRow").innerHTML = "";
    $("shout").hidden = true;
    $("tv").classList.remove("shake");
    $("overBox").hidden = true;
    overShown = false;
    cdKey = null;
}

/* ---------- building blocks ---------- */
function backNode(width) {
    const n = el("span", "card back");
    n.style.setProperty("--cw", `${width}px`);
    layer().appendChild(n);
    return n;
}

// A transform that puts the middle of `n` at point `c`.
function pose(n, c, rot = 0, scale = 1, dx = 0, dy = 0) {
    return `translate(${c.x - n.offsetWidth / 2 + dx}px, ${c.y - n.offsetHeight / 2 + dy}px) rotate(${rot}deg) scale(${scale})`;
}

// Animate a throwaway node and remove it afterwards. Always resolves.
function glide(n, keys, opts) {
    const a = n.animate(keys, Object.assign({ fill: "both", easing: EASE_OUT }, opts));
    return a.finished.then(() => n.remove(), () => n.remove());
}

function anchorEl(pid) {
    if (!view) return null;
    if (pid === view.you) return $("meAvatar");
    const s = seatEls.get(pid);
    return s ? s.av : null;
}
function anchorCenter(pid) {
    const a = anchorEl(pid);
    return a ? centerOf(rectOf(a)) : null;
}

function bubbleAt(x, y, text, kind) {
    const b = el("div", "bubble" + (kind ? " " + kind : ""), text);
    layer().appendChild(b);
    const bw = b.offsetWidth, bh = b.offsetHeight;
    const left = Math.max(6, Math.min(window.innerWidth - bw - 6, x - bw / 2));
    const top = Math.max(6, Math.min(window.innerHeight - bh - 6, y - bh / 2));
    b.style.transform = `translate(${left}px, ${top}px)`;
    const a = b.animate([
        { opacity: 0, transform: `translate(${left}px, ${top + 8}px) scale(.7)` },
        { opacity: 1, transform: `translate(${left}px, ${top}px) scale(1)`, offset: 0.14 },
        { opacity: 1, transform: `translate(${left}px, ${top}px) scale(1)`, offset: 0.82 },
        { opacity: 0, transform: `translate(${left}px, ${top - 6}px) scale(1)` }
    ], { duration: 1800, easing: "ease-out", fill: "both" });
    a.finished.then(() => b.remove(), () => b.remove());
}

// A speech bubble by a player's avatar: below it for opponents, above your status line for you.
function bubble(pid, text, kind) {
    const a = anchorEl(pid);
    if (!a) return;
    const r = rectOf(a);
    const c = centerOf(r);
    if (view && pid === view.you) {
        bubbleAt(c.x, rectOf($("statusLine")).top - 14, text, kind);
    } else {
        bubbleAt(c.x, c.y + r.height / 2 + 20, text, kind);
    }
}

function bumpPile() {
    const p = $("pile");
    p.classList.remove("bump");
    void p.offsetWidth;
    p.classList.add("bump");
}

/* ---------- the deal ---------- */
async function fxDeal(fresh, tok) {
    const c = centerOf(rectOf($("pile")));
    const pw = $("pile").offsetWidth;
    const jobs = [];
    let k = 0;
    for (let round = 0; round < 3; round++) {
        seatEls.forEach((s) => {
            const to = centerOf(rectOf(s.av));
            const n = backNode(pw * 0.7);
            jobs.push(glide(n, [
                { transform: pose(n, c, 0, 0.9), opacity: 1 },
                { transform: pose(n, to, 24, 0.55), opacity: 0.2 }
            ], { duration: 360, delay: k++ * 55 }));
        });
    }
    fresh.forEach((n, i) => {
        const r = rectOf(n);
        const dx = c.x - (r.left + r.width / 2), dy = c.y - (r.top + r.height / 2);
        jobs.push(n.animate([
            { transform: `translate(${dx}px, ${dy}px) scale(.45) rotate(-24deg)`, opacity: 0 },
            { transform: "none", opacity: 1 }
        ], { duration: 440, delay: 120 + i * 26, easing: EASE_OUT, fill: "backwards" }).finished.catch(() => {}));
    });
    await settle(jobs, tok);
}

/* ---------- a play: cards fly to the pile ---------- */
async function fxPlay(e, v, snap, tok) {
    const pile = centerOf(rectOf($("pile")));
    const pw = $("pile").offsetWidth;
    const jobs = [];
    const mine = e.by === v.you && snap && snap.mine && snap.mine.length ? snap.mine.slice(0, 8) : null;

    bubble(e.by, `${e.starts ? "Leads · " : ""}${e.count} × ${RANK_NAMES[e.rank]}`);

    if (mine) {
        mine.forEach((m, i) => {
            const n = cardEl(m.id, "span");
            n.style.setProperty("--cw", `${m.rect.width}px`);
            const backing = el("span", "card back overlay");   // fades in so the cards land face down
            n.appendChild(backing);
            layer().appendChild(n);
            const timing = { duration: 480, delay: i * 45 };
            backing.animate([{ opacity: 0 }, { opacity: 0, offset: 0.4 }, { opacity: 1, offset: 0.72 }, { opacity: 1 }],
                    Object.assign({ fill: "both" }, timing));
            const j = jit(i);
            jobs.push(glide(n, [
                { transform: pose(n, centerOf(m.rect)) },
                { transform: pose(n, pile, j.r, pw / m.rect.width, j.x, j.y) }
            ], timing));
        });
    } else {
        const from = anchorCenter(e.by);
        if (from) {
            const count = Math.min(e.count, 6);
            for (let i = 0; i < count; i++) {
                const n = backNode(pw);
                const j = jit(i);
                jobs.push(glide(n, [
                    { transform: pose(n, from, -10 + i * 6, 0.62), opacity: 1 },
                    { transform: pose(n, pile, j.r, 1, j.x, j.y), opacity: 1 }
                ], { duration: 460, delay: i * 70 }));
            }
        }
    }
    await settle(jobs, tok);
    bumpPile();
}

/* ---------- a pass ---------- */
async function fxPass(e, tok) {
    bubble(e.by, "Pass", "muted");
    const a = anchorEl(e.by);
    if (a) {
        a.classList.remove("wobble");
        void a.offsetWidth;
        a.classList.add("wobble");
        setTimeout(() => a.classList.remove("wobble"), 600);
    }
    await pause(420, tok);
}

/* ---------- the pile burns ---------- */
async function fxBurn(e, tok) {
    const r = rectOf($("pile"));
    const c = centerOf(r);
    const pw = $("pile").offsetWidth;
    const jobs = [];
    const count = Math.min(Math.max(e.count, 1), 6);
    const fire = "brightness(1.7) sepia(1) saturate(6) hue-rotate(-18deg)";

    for (let i = 0; i < count; i++) {
        const n = backNode(pw);
        const j = jit(i);
        jobs.push(glide(n, [
            { transform: pose(n, c, j.r, 1, j.x, j.y), filter: "none", opacity: 1 },
            { transform: pose(n, c, j.r, 1.04, j.x, j.y - 10), filter: fire, opacity: 1, offset: 0.4 },
            { transform: pose(n, c, j.r * 2, 0.8, j.x, j.y - 52), filter: `${fire} blur(2px)`, opacity: 0 }
        ], { duration: 900, delay: i * 40, easing: "ease-out" }));
    }
    for (let i = 0; i < 16; i++) {
        const em = el("span", "ember");
        layer().appendChild(em);
        const x = c.x + (Math.random() - 0.5) * r.width * 1.1;
        const y = c.y + (Math.random() - 0.2) * r.height * 0.6;
        const drift = (Math.random() - 0.5) * 50;
        jobs.push(glide(em, [
            { transform: `translate(${x}px, ${y}px) scale(1)`, opacity: 0 },
            { transform: `translate(${x + drift * 0.4}px, ${y - 22}px) scale(1)`, opacity: 1, offset: 0.2 },
            { transform: `translate(${x + drift}px, ${y - 90 - Math.random() * 50}px) scale(.2)`, opacity: 0 }
        ], { duration: 750 + Math.random() * 450, delay: Math.random() * 300, easing: "ease-out" }));
    }
    bubbleAt(c.x, c.y - r.height * 0.75 - 18, "Pile burned", "muted");
    await settle(jobs, tok);
}

/* ---------- a bluff call: shout, reveal, pick-up ---------- */
function makeFlip(id, rankIndex) {
    const hit = cardRank(id) === rankIndex;
    const root = el("div", "flip");
    const inner = el("div", "flip-inner");
    inner.append(el("span", "card back"), cardEl(id, "span", "face-side"));
    root.appendChild(inner);
    return {
        root,
        flip() {
            inner.animate([{ transform: "rotateY(0deg)" }, { transform: "rotateY(180deg)" }],
                    { duration: 420, easing: "cubic-bezier(.3,.7,.3,1)", fill: "forwards" });
            setTimeout(() => root.classList.add(hit ? "is-hit" : "is-miss"), 300);
        }
    };
}

async function fxCall(e, v, fresh, tok) {
    const stage = $("stage"), row = $("stageRow"), tv = $("tv"), shout = $("shout");
    const verdict = $("stageVerdict");
    const pileC = centerOf(rectOf($("pile")));
    const pw = $("pile").offsetWidth;

    try {
        row.innerHTML = "";
        $("stageClaim").textContent = "";
        $("stageSub").textContent = "";
        verdict.textContent = "";
        verdict.className = "stage-verdict";
        stage.classList.remove("out");

        // 1. the shout
        stage.hidden = false;
        $("shoutSub").textContent = `${who(e.caller)} ${verb(e.caller, "call", "calls")} on ${whoObj(e.accused)}`;
        shout.hidden = false;
        tv.classList.add("shake");
        buzz();
        await pause(800, tok);
        shout.hidden = true;
        tv.classList.remove("shake");

        // 2. the played cards slide out of the pile
        $("stageClaim").textContent =
                `${e.accused === v.you ? "You claimed" : `${nameOf(e.accused)} claimed`} ${e.cards.length} × ${RANK_NAMES[e.rankIndex]}`;
        const flips = e.cards.map((id) => makeFlip(id, e.rankIndex));
        flips.forEach((f) => row.appendChild(f.root));
        flips.forEach((f, i) => {
            const r = rectOf(f.root);
            const dx = pileC.x - (r.left + r.width / 2), dy = pileC.y - (r.top + r.height / 2);
            f.root.animate([
                { transform: `translate(${dx}px, ${dy}px) scale(.7)`, opacity: 0 },
                { transform: "none", opacity: 1 }
            ], { duration: 420, delay: i * 40, easing: EASE_OUT, fill: "backwards" });
        });
        await pause(420 + flips.length * 40 + 220, tok);

        // 3. flip them one at a time
        const step = Math.max(110, Math.min(340, 2400 / flips.length));
        for (const f of flips) { f.flip(); await pause(step, tok); }
        await pause(520, tok);

        // 4. the verdict
        verdict.textContent = `${who(e.accused)} ${verb(e.accused, "were", "was")} ${e.bluff ? "bluffing" : "telling the truth"}!`;
        verdict.classList.add(e.bluff ? "bad" : "good", "in");
        $("stageSub").textContent = `${who(e.loser)} ${verb(e.loser, "pick", "picks")} up the pile (${plural(e.picked, "card")})`;
        await pause(1250, tok);

        // 5. the loser scoops up everything
        fxHold.pile = 0;
        renderPile(0);
        const target = e.loser === v.you ? centerOf(rectOf($("hand"))) : (anchorCenter(e.loser) || pileC);
        stage.classList.add("out");
        const jobs = [];
        flips.forEach((f, i) => {
            const c = centerOf(rectOf(f.root));
            jobs.push(f.root.animate([
                { transform: "none", opacity: 1 },
                { transform: `translate(${target.x - c.x}px, ${target.y - c.y}px) scale(.4)`, opacity: 0.1 }
            ], { duration: 520, delay: i * 35, easing: EASE_IN, fill: "forwards" }).finished.catch(() => {}));
        });
        const extra = Math.min(Math.max(e.picked - e.cards.length, 0), 6);
        for (let i = 0; i < extra; i++) {
            const n = backNode(pw);
            jobs.push(glide(n, [
                { transform: pose(n, pileC, jit(i).r), opacity: 1 },
                { transform: pose(n, target, 0, 0.5), opacity: 0.2 }
            ], { duration: 520, delay: i * 40, easing: EASE_IN }));
        }
        await settle(jobs, tok);
    } finally {
        stage.hidden = true;
        stage.classList.remove("out");
        row.innerHTML = "";
        shout.hidden = true;
        tv.classList.remove("shake");
    }

    if (tok !== fxTok) throw CANCEL;
    bubble(e.loser, `+${e.picked}`, "danger");
    fresh.forEach((n, i) => {
        n.style.visibility = "";
        n.animate([
            { transform: "translateY(16px) scale(.6)", opacity: 0 },
            { transform: "none", opacity: 1 }
        ], { duration: 320, delay: Math.min(i, 20) * 20, easing: EASE_OUT, fill: "backwards" });
    });
}

function confetti() {
    if (reduceMotion()) return;
    const host = $("gameView");
    const colors = ["#d6b25e", "#e8806f", "#5fcf8e", "#6aa3ff", "#f2eee3"];
    for (let i = 0; i < 46; i++) {
        const bit = el("span", "confetti");
        bit.style.left = `${Math.random() * 100}%`;
        bit.style.background = colors[i % colors.length];
        bit.style.animationDelay = `${Math.random() * 0.8}s`;
        bit.style.animationDuration = `${2.4 + Math.random() * 1.4}s`;
        host.appendChild(bit);
        setTimeout(() => bit.remove(), 5000);
    }
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
    if (view && view.hand.some((c) => selected.has(c))) { const m = modeOf(view); renderDeclare(m); renderActions(m); }
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

$("leaveBtn").addEventListener("click", () => {
    if (view && view.phase === "playing" && !window.confirm("Leave this game?")) return;
    backToLobby("");
});

window.addEventListener("resize", () => { if (shown === "gameView") fitHand(); });

/* =====================================================================
   CONNECTIONS
   ===================================================================== */
function teardown() {
    // Clear state first so close events fired by the calls below see "we left on purpose".
    const guestConn = conn, hostConns = [...conns.values()], p = peer;
    conn = null; peer = null; role = null; game = null; view = null; lastView = null; shown = null;
    conns.clear();
    nextPid = 1; hostAttempts = 0; roomCode = ""; declRank = null;
    selected.clear();

    // table furniture and animations
    seenEvent = null; seatKey = ""; claimKey = "";
    seatEls.clear(); handEls.clear();
    $("handIn").innerHTML = "";
    ["oppTop", "oppLeft", "oppRight"].forEach((id) => { $(id).innerHTML = ""; });
    resetFx();

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