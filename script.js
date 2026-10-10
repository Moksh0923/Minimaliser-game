const clickSound = new Audio("https://www.soundjay.com/buttons/sounds/button-16.mp3");
const winSound = new Audio("https://www.soundjay.com/misc/sounds/bell-ringing-05.mp3");

const MIN_PLAYERS = 2;
const MAX_PLAYERS = 12;
const MAX_ROUNDS = 50;
const MAX_NAME_LENGTH = 20;
const STEPS = ["stepCount", "stepNames", "roundSection", "gameContainer"];

let players = [];
let currentRound = 1;
let totalRounds = 0;
let history = [];

/* ================= HELPERS ================= */
function $(id) {
    return document.getElementById(id);
}

function escapeHtml(value) {
    return String(value).replace(/[&<>"']/g, (c) => ({
        "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
    }[c]));
}

// Avoids floating point drift such as 0.1 + 0.2 so ties are detected correctly
function addScores(a, b) {
    return Number((a + b).toFixed(6));
}

function playSound(sound) {
    try {
        sound.currentTime = 0;
        const result = sound.play();
        if (result && typeof result.catch === "function") result.catch(() => {});
    } catch (e) {
        /* sound is optional */
    }
}

function parseIntegerInput(input, min, max) {
    const raw = input.value.trim();
    const n = Number(raw);
    if (raw === "" || !Number.isInteger(n) || n < min || n > max) return null;
    return n;
}

function markInvalid(input, invalid) {
    if (invalid) input.setAttribute("aria-invalid", "true");
    else input.removeAttribute("aria-invalid");
}

function setError(id, message) {
    $(id).textContent = message || "";
}

function joinNames(names) {
    if (names.length <= 2) return names.join(" and ");
    return names.slice(0, -1).join(", ") + " and " + names[names.length - 1];
}

// Shows one step at a time and moves focus into it
function showStep(id) {
    STEPS.forEach((step) => {
        $(step).hidden = step !== id;
    });
    const step = $(id);
    const target = step.querySelector("input") || step.querySelector("h2");
    if (target) target.focus();
}

/* ================= EFFECTS ================= */
function confetti() {
    if (window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches) return;

    const colors = ["#d6b25e", "#ece6d6", "#7f9c8c", "#b8923f"];
    for (let i = 0; i < 40; i++) {
        let div = document.createElement("div");
        div.className = "confetti";
        div.style.left = Math.random() * 100 + "vw";
        div.style.background = colors[i % colors.length];
        div.style.animationDelay = Math.random() * 0.6 + "s";
        div.style.animationDuration = 2.2 + Math.random() * 1.4 + "s";
        document.body.appendChild(div);

        setTimeout(() => div.remove(), 4500);
    }
}

/* ================= SETUP ================= */
function startApp() {
    $("startScreen").hidden = true;
    $("mainApp").hidden = false;
    showStep("stepCount");
}

function createPlayers() {
    const countInput = $("numPlayers");
    const num = parseIntegerInput(countInput, MIN_PLAYERS, MAX_PLAYERS);

    if (num === null) {
        markInvalid(countInput, true);
        setError("numPlayersError", `Enter a whole number from ${MIN_PLAYERS} to ${MAX_PLAYERS}.`);
        countInput.focus();
        return;
    }
    markInvalid(countInput, false);
    setError("numPlayersError", "");

    let container = $("playersContainer");
    // Keep names already typed if the person goes back and changes the count
    const previous = Array.from(container.querySelectorAll("input")).map((i) => i.value);
    container.innerHTML = "";

    for (let i = 0; i < num; i++) {
        const field = document.createElement("div");
        field.className = "field";

        const label = document.createElement("label");
        label.htmlFor = `playerName-${i}`;
        label.textContent = `Player ${i + 1}`;

        const input = document.createElement("input");
        input.type = "text";
        input.id = `playerName-${i}`;
        input.placeholder = "Enter name";
        input.maxLength = MAX_NAME_LENGTH;
        input.autocomplete = "off";
        input.value = previous[i] || "";
        input.setAttribute("data-advance", "");
        input.setAttribute("aria-describedby", "playersError");
        input.setAttribute("enterkeyhint", i === num - 1 ? "done" : "next");

        field.append(label, input);
        container.appendChild(field);
    }

    setError("playersError", "");
    showStep("stepNames");
}

function savePlayers() {
    const inputs = Array.from($("playersContainer").getElementsByTagName("input"));
    const seen = new Set();
    let firstBad = null;
    let message = "";

    inputs.forEach((input) => {
        const name = input.value.trim().replace(/\s+/g, " ");
        const key = name.toLowerCase();
        let problem = "";

        if (!name) problem = "Enter a name for every player.";
        else if (seen.has(key)) problem = "Each player needs a different name.";

        markInvalid(input, Boolean(problem));
        if (problem && !firstBad) {
            firstBad = input;
            message = problem;
        }
        seen.add(key);
    });

    if (firstBad) {
        setError("playersError", message);
        firstBad.focus();
        return;
    }

    setError("playersError", "");
    // Rebuilt each time, so saving again never duplicates players
    players = inputs.map((input) => ({
        name: input.value.trim().replace(/\s+/g, " "),
        total: 0
    }));

    showStep("roundSection");
}

function startGame() {
    const roundsInput = $("numRounds");
    const n = parseIntegerInput(roundsInput, 1, MAX_ROUNDS);

    if (n === null) {
        markInvalid(roundsInput, true);
        setError("numRoundsError", `Enter a whole number from 1 to ${MAX_ROUNDS}.`);
        roundsInput.focus();
        return;
    }
    markInvalid(roundsInput, false);
    setError("numRoundsError", "");

    totalRounds = n;
    currentRound = 1;
    history = [];
    players.forEach((p) => { p.total = 0; });

    showRound();
}

/* ================= PLAY ================= */
function progressHTML(done) {
    const pct = totalRounds ? (done / totalRounds) * 100 : 0;
    return `
    <div class="progress" role="progressbar" aria-label="Rounds completed"
         aria-valuemin="0" aria-valuemax="${totalRounds}" aria-valuenow="${done}">
        <span style="width:${pct}%"></span>
    </div>`;
}

function showRound() {
    let container = $("gameContainer");

    container.innerHTML = `
    <p class="eyebrow">Round ${currentRound} of ${totalRounds}</p>
    ${progressHTML(currentRound - 1)}
    <h2 tabindex="-1">Enter scores</h2>
    <form id="scoreForm" novalidate>
        <ul class="score-list">
            ${players.map((p, i) => `
            <li class="score-row">
                <label for="score-${i}">${escapeHtml(p.name)}<span class="sr-only"> score</span></label>
                <input type="number" id="score-${i}" step="any" placeholder="Score"
                       autocomplete="off" data-advance aria-describedby="scoreError"
                       enterkeyhint="${i === players.length - 1 ? "done" : "next"}">
            </li>`).join("")}
        </ul>
        <p class="error" id="scoreError" role="alert"></p>
        <div class="actions">
            <button type="submit" class="btn btn-primary">Submit round</button>
        </div>
    </form>`;

    $("scoreForm").addEventListener("submit", (e) => {
        e.preventDefault();
        submitRound();
    });

    showStep("gameContainer");
}

function submitRound() {
    let inputs = Array.from($("scoreForm").getElementsByTagName("input"));

    let firstBad = null;
    inputs.forEach((input) => {
        const bad = input.value.trim() === "" || !Number.isFinite(Number(input.value));
        markInvalid(input, bad);
        if (bad && !firstBad) firstBad = input;
    });

    if (firstBad) {
        setError("scoreError", "Enter a score for every player.");
        firstBad.focus();
        return;
    }

    playSound(clickSound);

    let roundData = players.map((player, i) => ({
        name: player.name,
        score: Number(inputs[i].value)
    }));
    history.push(roundData);

    // Update scores
    players.forEach((player, i) => {
        player.total = addScores(player.total, roundData[i].score);
    });

    currentRound++;

    // More rounds -> standings with a Next Round button; otherwise final result
    if (currentRound <= totalRounds) {
        showLeaderboard();
    } else {
        showWinner();
    }
}

/* ================= RANKING & TABLES ================= */
// Lowest total ranks first. Equal totals share a rank (1, 1, 3).
function rankPlayers() {
    const sorted = [...players].sort((a, b) => a.total - b.total);
    let rank = 0;
    let previous = null;

    return sorted.map((player, index) => {
        if (player.total !== previous) {
            rank = index + 1;
            previous = player.total;
        }
        return { name: player.name, total: player.total, rank };
    });
}

function leaderboardHTML(caption) {
    const rows = rankPlayers().map((p) => `
        <tr class="${p.rank === 1 ? "is-leader" : ""}">
            <td class="rank">${p.rank}</td>
            <th scope="row">${escapeHtml(p.name)}</th>
            <td class="total">${p.total}</td>
        </tr>`).join("");

    return `
    <table class="board">
        <caption class="sr-only">${caption}</caption>
        <thead>
            <tr>
                <th scope="col" class="col-rank">Rank</th>
                <th scope="col">Player</th>
                <th scope="col" class="col-total">Total</th>
            </tr>
        </thead>
        <tbody>${rows}</tbody>
    </table>`;
}

function historyHTML(open) {
    if (!history.length) return "";

    const head = history.map((_, r) => `<th scope="col">R${r + 1}</th>`).join("");
    const rows = players.map((p, i) => `
        <tr>
            <th scope="row">${escapeHtml(p.name)}</th>
            ${history.map((round) => `<td>${round[i].score}</td>`).join("")}
            <td class="sum">${p.total}</td>
        </tr>`).join("");

    return `
    <details class="history"${open ? " open" : ""}>
        <summary>Round history</summary>
        <div class="table-scroll" role="region" aria-label="Round history" tabindex="0">
            <table class="history-table">
                <thead><tr><th scope="col">Player</th>${head}<th scope="col">Total</th></tr></thead>
                <tbody>${rows}</tbody>
            </table>
        </div>
    </details>`;
}

/* ================= SCREENS ================= */
function showLeaderboard() {
    let container = $("gameContainer");
    const done = currentRound - 1;

    container.innerHTML = `
    <p class="eyebrow">After round ${done} of ${totalRounds}</p>
    ${progressHTML(done)}
    <h2 tabindex="-1">Standings</h2>
    ${leaderboardHTML("Standings, lowest total first")}
    ${historyHTML(false)}
    <div class="actions">
        <button type="button" class="btn btn-primary" id="nextRoundBtn">Next round</button>
    </div>`;

    $("nextRoundBtn").addEventListener("click", showRound);
    showStep("gameContainer");
}

function showWinner() {
    let container = $("gameContainer");

    const ranked = rankPlayers();
    const best = ranked[0].total;
    const winners = ranked.filter((p) => p.total === best);
    const tie = winners.length > 1;

    container.innerHTML = `
    <p class="eyebrow">Final result · ${totalRounds} ${totalRounds === 1 ? "round" : "rounds"}</p>
    ${progressHTML(totalRounds)}
    <div class="result">
        <h2 tabindex="-1">${tie ? "Tied winners" : "Winner"}</h2>
        <p class="result-names">${escapeHtml(joinNames(winners.map((w) => w.name)))}</p>
        <p class="result-detail">${tie ? "Shared lowest total" : "Lowest total"}: ${best}</p>
    </div>
    <h3 class="section-label">Final standings</h3>
    ${leaderboardHTML("Final standings, lowest total first")}
    ${historyHTML(true)}
    <div class="actions">
        <button type="button" class="btn btn-primary" id="newGameBtn">New game</button>
    </div>`;

    $("newGameBtn").addEventListener("click", newGame);
    showStep("gameContainer");

    playSound(winSound);
    confetti();
}

function newGame() {
    players = [];
    history = [];
    currentRound = 1;
    totalRounds = 0;

    ["numPlayers", "numRounds"].forEach((id) => {
        $(id).value = "";
        markInvalid($(id), false);
    });
    ["numPlayersError", "numRoundsError", "playersError"].forEach((id) => setError(id, ""));
    $("playersContainer").innerHTML = "";
    $("gameContainer").innerHTML = "";

    showStep("stepCount");
}

/* ================= KEYBOARD & VALIDATION UX ================= */
// Enter moves to the next field; on the last field it submits the form
document.addEventListener("keydown", (e) => {
    if (e.key !== "Enter" || e.isComposing) return;
    const input = e.target;
    if (!input.matches || !input.matches("input[data-advance]")) return;

    const fields = Array.from(input.form.querySelectorAll("input[data-advance]"));
    const index = fields.indexOf(input);
    if (index > -1 && index < fields.length - 1) {
        e.preventDefault();
        fields[index + 1].focus();
    }
});

// Clear the red state as soon as the person edits a field
document.addEventListener("input", (e) => {
    if (e.target.matches && e.target.matches("input[aria-invalid]")) {
        markInvalid(e.target, false);
    }
});
