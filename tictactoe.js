/* Live two-device tic tac toe.
   Uses PeerJS (WebRTC). The host's peer ID is derived from the party code, so the
   guest connects directly to the host. The host is the referee: it validates every
   move and broadcasts the full game state. */

const ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"; // no 0/O/1/I
const PREFIX = "minimaliser-ttt-";
const CODE_LENGTH = 5;
const LINES = [[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],[0,4,8],[2,4,6]];

const $ = (id) => document.getElementById(id);
const VIEWS = ["lobby", "hostView", "joinView", "gameView"];

let peer = null;
let conn = null;
let role = null;            // "host" (plays X) or "guest" (plays O)
let state = null;
let hostAttempts = 0;

/* ---------- view helpers ---------- */
function show(id) {
    VIEWS.forEach((v) => { $(v).hidden = v !== id; });
    const el = $(id).querySelector("input") || $(id).querySelector("h2");
    if (el) el.focus();
}

function mySymbol() { return role === "host" ? "X" : "O"; }

function teardown() {
    if (conn) { try { conn.close(); } catch (e) {} }
    if (peer) { try { peer.destroy(); } catch (e) {} }
    conn = null; peer = null; role = null; state = null; hostAttempts = 0;
}

function backToLobby(message) {
    teardown();
    $("lobbyError").textContent = message || "";
    $("joinError").textContent = "";
    $("codeInput").value = "";
    show("lobby");
}

function makeCode() {
    let code = "";
    const bytes = crypto.getRandomValues(new Uint8Array(CODE_LENGTH));
    bytes.forEach((b) => { code += ALPHABET[b % ALPHABET.length]; });
    return code;
}

function peerLibMissing() {
    if (typeof Peer !== "undefined") return false;
    $("lobbyError").textContent = "Couldn't load the online connection library. Check your internet and reload.";
    return true;
}

/* ---------- game state (host only mutates) ---------- */
function freshState(scores, starter) {
    return {
        board: Array(9).fill(null),
        turn: starter,
        starter,
        winner: null,      // "X" | "O" | "draw" | null
        line: null,
        scores: scores || { X: 0, O: 0, draw: 0 }
    };
}

function hostApplyMove(i, symbol) {
    const s = state;
    if (s.winner || s.turn !== symbol || !Number.isInteger(i) || i < 0 || i > 8 || s.board[i]) return;
    s.board[i] = symbol;

    const line = LINES.find(([a, b, c]) => s.board[a] && s.board[a] === s.board[b] && s.board[a] === s.board[c]);
    if (line) {
        s.winner = symbol; s.line = line; s.scores[symbol]++;
    } else if (s.board.every(Boolean)) {
        s.winner = "draw"; s.scores.draw++;
    } else {
        s.turn = symbol === "X" ? "O" : "X";
    }
    broadcast();
}

function hostRematch() {
    if (!state || !state.winner) return;
    state = freshState(state.scores, state.starter === "X" ? "O" : "X");
    broadcast();
}

function broadcast() {
    render();
    if (conn && conn.open) conn.send({ type: "state", state });
}

/* ---------- rendering ---------- */
function buildBoard() {
    const board = $("board");
    board.innerHTML = "";
    for (let i = 0; i < 9; i++) {
        const b = document.createElement("button");
        b.type = "button";
        b.className = "cell";
        b.dataset.index = i;
        b.addEventListener("click", () => onCell(i));
        board.appendChild(b);
    }
}

function render() {
    if (!state) return;
    const me = mySymbol();
    const over = Boolean(state.winner);

    $("roleLine").textContent = `You are ${me} · ${role === "host" ? "host" : "guest"}`;

    let status;
    if (state.winner === "draw") status = "It's a draw";
    else if (state.winner) status = state.winner === me ? "You win" : "Your friend wins";
    else status = state.turn === me ? "Your turn" : "Friend's turn";
    $("statusLine").textContent = status;

    [...$("board").children].forEach((cell, i) => {
        const mark = state.board[i];
        cell.textContent = mark || "";
        if (mark) cell.dataset.mark = mark; else delete cell.dataset.mark;
        cell.disabled = over || Boolean(mark) || state.turn !== me;
        cell.classList.toggle("win", Boolean(state.line && state.line.includes(i)));
        const r = Math.floor(i / 3) + 1, c = (i % 3) + 1;
        cell.setAttribute("aria-label", `Row ${r}, column ${c}, ${mark || "empty"}`);
    });

    const other = me === "X" ? "O" : "X";
    $("scores").innerHTML = `
        <div><dt>You (${me})</dt><dd>${state.scores[me]}</dd></div>
        <div><dt>Draws</dt><dd>${state.scores.draw}</dd></div>
        <div><dt>Friend (${other})</dt><dd>${state.scores[other]}</dd></div>`;

    $("againBtn").hidden = !over;
}

function onCell(i) {
    if (!state || state.winner || state.turn !== mySymbol()) return;
    if (role === "host") hostApplyMove(i, "X");
    else if (conn && conn.open) conn.send({ type: "move", i });
}

/* ---------- connection wiring ---------- */
function wireConnection(c) {
    conn = c;

    c.on("data", (msg) => {
        if (!msg || typeof msg !== "object") return;
        if (role === "host") {
            if (msg.type === "move") hostApplyMove(msg.i, "O");
            if (msg.type === "rematch") hostRematch();
        } else if (msg.type === "state") {
            const first = !state;
            state = msg.state;
            if (first) { buildBoard(); show("gameView"); }
            render();
        }
    });

    c.on("close", () => {
        if (!peer) return; // we left on purpose
        backToLobby("Your friend left the party.");
    });
    c.on("error", () => backToLobby("The connection was lost."));
}

/* ---------- host ---------- */
function startHosting() {
    if (peerLibMissing()) return;
    $("lobbyError").textContent = "";
    $("partyCode").textContent = "…";
    $("hostStatus").textContent = "Creating party…";
    $("copyBtn").disabled = true;
    show("hostView");
    openHostPeer();
}

function openHostPeer() {
    const code = makeCode();
    const p = new Peer(PREFIX + code);
    peer = p;

    p.on("open", () => {
        role = "host";
        $("partyCode").textContent = code;
        $("hostStatus").textContent = "Waiting for your friend to join…";
        $("copyBtn").disabled = false;
    });

    p.on("connection", (c) => {
        if (conn && conn.open) { c.on("open", () => c.close()); return; } // party is full
        wireConnection(c);
        c.on("open", () => {
            state = freshState(null, "X");
            buildBoard();
            show("gameView");
            broadcast();
        });
    });

    p.on("disconnected", () => { try { p.reconnect(); } catch (e) {} });

    p.on("error", (err) => {
        if (err.type === "unavailable-id" && hostAttempts < 5) {
            hostAttempts++;
            try { p.destroy(); } catch (e) {}
            openHostPeer();
        } else {
            backToLobby("Couldn't create a party. Check your connection and try again.");
        }
    });
}

/* ---------- guest ---------- */
function joinParty(code) {
    if (peerLibMissing()) { show("lobby"); return; }
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
        markInvalid(true);
        $("codeInput").focus();
    };

    const timeout = setTimeout(() => fail("Couldn't reach that party. Check the code and try again."), 12000);

    p.on("open", () => {
        const c = p.connect(PREFIX + code, { reliable: true });
        c.on("open", () => {
            if (settled) return;
            settled = true;
            clearTimeout(timeout);
            btn.disabled = false;
            wireConnection(c);
            role = "guest";
            // game screen appears when the host sends the first state
        });
    });

    p.on("error", (err) => {
        clearTimeout(timeout);
        if (err.type === "peer-unavailable") fail("No party found with that code.");
        else if (settled) backToLobby("The connection was lost.");
        else fail("Couldn't connect. Check your internet and try again.");
    });
}

function markInvalid(bad) {
    if (bad) $("codeInput").setAttribute("aria-invalid", "true");
    else $("codeInput").removeAttribute("aria-invalid");
}

/* ---------- events ---------- */
$("hostBtn").addEventListener("click", startHosting);
$("joinBtn").addEventListener("click", () => { $("joinError").textContent = ""; markInvalid(false); show("joinView"); });

document.querySelectorAll("[data-leave]").forEach((b) =>
    b.addEventListener("click", () => backToLobby("")));

$("homeLink").addEventListener("click", () => teardown());
window.addEventListener("pagehide", () => teardown());

$("codeInput").addEventListener("input", (e) => {
    e.target.value = e.target.value.toUpperCase().replace(/[^A-Z0-9]/g, "");
    markInvalid(false);
});

$("joinForm").addEventListener("submit", (e) => {
    e.preventDefault();
    const code = $("codeInput").value.trim().toUpperCase();
    if (code.length !== CODE_LENGTH) {
        $("joinError").textContent = `Enter the ${CODE_LENGTH}-character code from the host.`;
        markInvalid(true);
        $("codeInput").focus();
        return;
    }
    joinParty(code);
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

$("againBtn").addEventListener("click", () => {
    if (role === "host") hostRematch();
    else if (conn && conn.open) conn.send({ type: "rematch" });
});
