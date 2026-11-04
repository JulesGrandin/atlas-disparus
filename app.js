const REVEAL_MS = 2000;
const MIN_BORDER_KM = 8;
const EARTH_KM = 6371;
const US_SKIP = new Set(["AK", "HI", "DC"]);

const FRAMES = {
  europe: { center: [15, 54], west: -25, east: 42, south: 34, north: 71 },
  africa: { center: [17, 1.3], west: -18, east: 52, south: -36, north: 38 },
  asia: { center: [88, 32], west: 26, east: 146, south: -11, north: 72 },
  us: { center: [-97, 39], west: -128, east: -65, south: 15, north: 58 },
};

const EUROPE = ["ALB", "DEU", "AUT", "BEL", "BLR", "BIH", "BGR", "CYP", "HRV", "DNK", "ESP", "EST", "FIN", "FRA", "GRC", "HUN", "ISL", "IRL", "ITA", "KOS", "LVA", "LTU", "LUX", "MKD", "MDA", "MNE", "NOR", "NLD", "POL", "PRT", "CZE", "ROU", "GBR", "RUS", "SRB", "SVK", "SVN", "SWE", "CHE", "UKR", "TUR"];
const AFRICA = ["DZA", "AGO", "BEN", "BWA", "BFA", "BDI", "CMR", "CAF", "TCD", "COG", "COD", "CIV", "EGY", "ERI", "SWZ", "ETH", "GAB", "GHA", "GIN", "GNB", "GNQ", "KEN", "LSO", "LBR", "LBY", "MDG", "MWI", "MLI", "MRT", "MAR", "MOZ", "NAM", "NER", "NGA", "UGA", "RWA", "SEN", "SLE", "SOM", "ZAF", "SDS", "SDN", "TZA", "TGO", "TUN", "ZMB", "ZWE"];
const ASIA = ["AFG", "SAU", "ARM", "AZE", "BGD", "MMR", "KHM", "CHN", "PRK", "KOR", "ARE", "GEO", "IND", "IDN", "IRN", "IRQ", "JPN", "JOR", "KAZ", "KGZ", "LAO", "MYS", "MNG", "NPL", "OMN", "UZB", "PAK", "PHL", "RUS", "LKA", "SYR", "TJK", "TWN", "THA", "TUR", "TKM", "VNM", "YEM"];

const ZONE_IDS = {
  europe: new Set(EUROPE),
  africa: new Set(AFRICA),
  asia: new Set(ASIA),
};

const LEAD = {
  europe: "Deux pays ont été fusionnés sur la carte de l'Europe.<br>Sauras-tu les retrouver ?",
  africa: "Deux pays ont été fusionnés sur la carte de l'Afrique.<br>Sauras-tu les retrouver ?",
  asia: "Deux pays ont été fusionnés sur la carte de l'Asie.<br>Sauras-tu les retrouver ?",
  us: "Deux États ont été fusionnés sur la carte des États-Unis.<br>Sauras-tu les retrouver ?",
};

const RESULT_LEAD = {
  europe: "Les deux pays fusionnés étaient…",
  africa: "Les deux pays fusionnés étaient…",
  asia: "Les deux pays fusionnés étaient…",
  us: "Les deux États fusionnés étaient…",
};

const mobileLayout = window.matchMedia("(max-width: 720px)");
const frameCompact = window.matchMedia("(max-width: 640px)");

const els = {
  load: document.getElementById("load-overlay"),
  loadText: document.getElementById("load-text"),
  loadBar: document.getElementById("load-bar"),
  loadFill: document.getElementById("load-bar-fill"),
  intro: document.getElementById("intro-modal"),
  lead: document.getElementById("intro-lead"),
  chrome: document.getElementById("chrome"),
  roundKicker: document.getElementById("round-kicker"),
  roundPrompt: document.getElementById("round-prompt"),
  result: document.getElementById("result-modal"),
  resultKicker: document.getElementById("result-kicker"),
  resultPrompt: document.getElementById("result-prompt"),
  resultLead: document.getElementById("result-lead"),
  resultLabel: document.getElementById("result-label"),
  resultMark: document.getElementById("result-mark"),
  btnNext: document.getElementById("btn-next"),
  reviewBar: document.getElementById("review-bar"),
  notes: document.getElementById("map-notes"),
  noteMiss: document.getElementById("note-miss"),
  noteMissName: document.getElementById("note-miss-name"),
  noteFusion: document.getElementById("note-fusion"),
  noteFusionKicker: document.getElementById("note-fusion-kicker"),
  noteFusionName: document.getElementById("note-fusion-name"),
  verdict: document.getElementById("verdict"),
  historyWrap: document.getElementById("history-wrap"),
  history: document.getElementById("history"),
  timerBlock: document.getElementById("timer-block"),
  timerBar: document.getElementById("timer-bar"),
  timerFill: document.getElementById("timer-fill"),
  timerValue: document.getElementById("timer-value"),
  finish: document.getElementById("finish-modal"),
  finalScore: document.getElementById("final-score"),
  finishRecap: document.getElementById("finish-recap"),
  map: document.getElementById("map"),
};

const projection = d3.geoOrthographic().clipAngle(90).precision(0.4);
const geoPath = d3.geoPath(projection);
const view = { width: 0, height: 0 };

const game = {
  zone: "europe",
  length: 5,
  roundMs: 10000,
  queue: [],
  index: 0,
  rounds: [],
  live: false,
  pair: null,
};

let countries = [];
let states = [];
let countryBorders = [];
let stateBorders = [];
let coast = { type: "MultiLineString", coordinates: [] };
let lakes = [];
let zonePairs = { europe: [], africa: [], asia: [] };
let countryById = new Map();
let stateById = new Map();
let timerFrame = 0;
let verdictFrame = 0;
let verdictTimer = 0;
let resultReveal = 0;
let notesOpen = false;
let ready = false;
let placed = false;
let globeSpin = null;
const fitSamples = {};
const mapView = { scale: 1, x: 0, y: 0 };
const mapPointers = new Map();
let mapPinch = null;
let blockMapClickUntil = 0;

const svg = d3.select(els.map)
  .append("svg")
  .attr("role", "img")
  .attr("aria-label", "Carte des pays");
const defs = svg.append("defs");
const seaPattern = defs.append("pattern")
  .attr("id", "sea-texture")
  .attr("patternUnits", "userSpaceOnUse")
  .attr("width", 1920)
  .attr("height", 1080);
seaPattern.append("image")
  .attr("href", "texture-fond.png")
  .attr("width", 1920)
  .attr("height", 1080);
const landMask = defs.append("mask").attr("id", "land-mask").attr("maskUnits", "userSpaceOnUse");
const maskRect = landMask.append("rect").attr("fill", "#fff");
const maskLakes = landMask.append("g").attr("fill", "#000");
const shadowPath = svg.append("path").attr("class", "globe-shadow").attr("filter", "url(#globe-shadow)");
const shadowFilter = defs.append("filter")
  .attr("id", "globe-shadow")
  .attr("x", "-25%")
  .attr("y", "-25%")
  .attr("width", "150%")
  .attr("height", "150%");
shadowFilter.append("feGaussianBlur").attr("stdDeviation", 16);
const spherePath = svg.append("path").attr("class", "sphere");
const landLayer = svg.append("g").attr("class", "land").attr("mask", "url(#land-mask)");
const countryLayer = landLayer.append("g");
const stateLayer = landLayer.append("g");
const fusionPath = landLayer.append("path").attr("class", "fusion").attr("display", "none");
const borderLayer = landLayer.append("g").attr("class", "borders");
const stateBorderLayer = landLayer.append("g").attr("class", "borders");
const lakeLayer = svg.append("g");
const coastPath = svg.append("path").attr("class", "outline");

let countryPaths = countryLayer.selectAll("path");
let statePaths = stateLayer.selectAll("path");
let borderPaths = borderLayer.selectAll("path");
let stateBorderPaths = stateBorderLayer.selectAll("path");
let lakeMaskPaths = maskLakes.selectAll("path");
let lakePaths = lakeLayer.selectAll("path");

document.querySelectorAll(".mode-switch").forEach((group) => {
  group.querySelectorAll("button").forEach((button) => {
    button.addEventListener("click", () => {
      group.querySelectorAll("button").forEach((other) => {
        other.setAttribute("aria-pressed", other === button ? "true" : "false");
      });
      if (group.id === "zone-switch") selectZone(button.dataset.zone);
    });
  });
});

document.getElementById("btn-start").addEventListener("click", startGame);
els.btnNext.addEventListener("click", onNext);
document.getElementById("btn-review").addEventListener("click", showMap);
document.getElementById("btn-back").addEventListener("click", showResultAgain);
document.getElementById("btn-replay").addEventListener("click", showIntro);
svg.on("click", onMapClick);
const mapNode = svg.node();
mapNode.addEventListener("pointerdown", onMapPointerDown);
mapNode.addEventListener("pointermove", onMapPointerMove);
mapNode.addEventListener("pointerup", onMapPointerEnd);
mapNode.addEventListener("pointercancel", onMapPointerEnd);
new ResizeObserver(() => layout()).observe(els.map);

load().catch((error) => {
  console.error(error);
  els.loadText.textContent = "Le fond de carte n'a pas pu être chargé.";
});

async function load() {
  setProgress(8);
  const [countryFile, lakeFile, stateFile] = await Promise.all([
    fetch("data/countries-all-50m.json").then((response) => response.json()),
    fetch("data/lakes-50m.json").then((response) => response.json()),
    fetch("data/us-states-10m.geojson").then((response) => response.json()),
  ]);
  setProgress(28);
  buildPlaces(countryFile, stateFile, lakeFile);
  const countryEdges = await sharedBorders(countries, 28, 62);
  countryBorders = countryEdges.borders;
  coast = countryEdges.coast;
  const stateEdges = await sharedBorders(states.filter((state) => !US_SKIP.has(state.id)), 62, 88);
  stateBorders = stateEdges.borders;
  zonePairs = {
    europe: countryBorders.filter((border) => ZONE_IDS.europe.has(border.a) && ZONE_IDS.europe.has(border.b)),
    africa: countryBorders.filter((border) => ZONE_IDS.africa.has(border.a) && ZONE_IDS.africa.has(border.b)),
    asia: countryBorders.filter((border) => ZONE_IDS.asia.has(border.a) && ZONE_IDS.asia.has(border.b)),
  };
  setProgress(94);
  drawBase();
  ready = true;
  selectZone("europe");
  setProgress(100);
  requestAnimationFrame(() => {
    els.load.classList.add("is-done");
    els.load.setAttribute("aria-busy", "false");
  });
}

function buildPlaces(countryFile, stateFile, lakeFile) {
  const byId = new Map(countryFile.features.map((feature) => [feature.properties.ADM0_A3, feature]));
  absorb(byId, "SOM", "SOL");
  absorb(byId, "CYP", "CYN");
  countries = [...byId.values()]
    .filter((feature) => feature.properties.ADM0_A3 !== "ATA")
    .map((feature) => ({
      id: feature.properties.ADM0_A3,
      name: feature.properties.ADM0_A3 === "CHN" ? "Chine" : (feature.properties.NAME_FR || feature.properties.NAME),
      geometry: feature.geometry,
    }));
  countryById = new Map(countries.map((country) => [country.id, country]));
  states = stateFile.features
    .filter((feature) => feature.properties.postal !== "DC" && feature.properties.type !== "Federal District")
    .map((feature) => ({
      id: feature.properties.postal,
      name: String(feature.properties.name_fr || feature.properties.name).replace(/^État de /, "").replace(/^Etat de /, ""),
      geometry: feature.geometry,
    }));
  stateById = new Map(states.map((state) => [state.id, state]));
  lakes = lakeFile.features.filter((feature) => Number(feature.properties.scalerank) <= 2);
}

function absorb(byId, primaryId, extraId) {
  const primary = byId.get(primaryId);
  const extra = byId.get(extraId);
  if (!primary || !extra) return;
  byId.set(primaryId, {
    type: "Feature",
    properties: primary.properties,
    geometry: {
      type: "MultiPolygon",
      coordinates: polygonParts(primary).concat(polygonParts(extra)),
    },
  });
  byId.delete(extraId);
}

function drawBase() {
  countryPaths = countryLayer.selectAll("path")
    .data(countries, (country) => country.id)
    .join("path")
    .attr("class", "unit")
    .attr("data-id", (country) => country.id);
  statePaths = stateLayer.selectAll("path")
    .data(states, (state) => state.id)
    .join("path")
    .attr("class", "unit")
    .attr("data-id", (state) => state.id);
  borderPaths = borderLayer.selectAll("path")
    .data(countryBorders, (border) => border.key)
    .join("path")
    .attr("class", "border");
  stateBorderPaths = stateBorderLayer.selectAll("path")
    .data(stateBorders, (border) => border.key)
    .join("path")
    .attr("class", "border");
  lakeMaskPaths = maskLakes.selectAll("path")
    .data(lakes)
    .join("path");
  lakePaths = lakeLayer.selectAll("path")
    .data(lakes)
    .join("path")
    .attr("class", "lake");
}

async function sharedBorders(units, progressFrom, progressTo) {
  const seen = new Map();
  const groups = new Map();
  for (let index = 0; index < units.length; index += 1) {
    const unit = units[index];
    polygonParts(unit).forEach((polygon) => {
      polygon.forEach((ring) => {
        for (let i = 0; i < ring.length - 1; i += 1) {
          const start = ring[i];
          const end = ring[i + 1];
          const key = edgeKey(start, end);
          if (!key) continue;
          const prev = seen.get(key);
          if (!prev) {
            seen.set(key, { id: unit.id, line: [start, end], km: kmBetween(start, end) });
            continue;
          }
          if (prev.id === unit.id || prev.id === "shared") continue;
          const keyPair = pairKey(prev.id, unit.id);
          let group = groups.get(keyPair);
          if (!group) {
            group = { key: keyPair, a: prev.id, b: unit.id, lines: [], km: 0 };
            groups.set(keyPair, group);
          }
          group.lines.push(prev.line);
          group.km += prev.km;
          seen.set(key, { id: "shared" });
        }
      });
    });
    if (index % 24 === 0) {
      setProgress(progressFrom + (progressTo - progressFrom) * index / units.length);
      await nextFrame();
    }
  }
  const coastLines = [];
  seen.forEach((item) => {
    if (item.line) coastLines.push(item.line);
  });
  const borders = [];
  groups.forEach((group) => {
    if (group.km < MIN_BORDER_KM) return;
    borders.push({
      key: group.key,
      a: group.a,
      b: group.b,
      geometry: { type: "MultiLineString", coordinates: chainLines(group.lines) },
    });
  });
  return { borders, coast: { type: "MultiLineString", coordinates: coastLines } };
}

function selectZone(zone) {
  game.zone = zone;
  els.lead.innerHTML = LEAD[zone];
  svg.attr("aria-label", zone === "us" ? "Carte des États des USA" : "Carte des pays");
  if (!ready) return;
  if (document.body.classList.contains("is-playing") || !placed) layout();
  else flyToFrame();
}

function selectedZone() {
  const button = document.querySelector("#zone-switch button[aria-pressed='true']");
  return button ? button.dataset.zone : "europe";
}

function startGame() {
  const lengthButton = document.querySelector("#length-switch button[aria-pressed='true']");
  const paceButton = document.querySelector("#pace-switch button[aria-pressed='true']");
  game.zone = selectedZone();
  game.length = Number(lengthButton.dataset.length);
  game.roundMs = Number(paceButton.dataset.ms);
  game.queue = [];
  game.index = 0;
  game.rounds = [];
  els.intro.hidden = true;
  els.finish.hidden = true;
  els.chrome.hidden = false;
  els.historyWrap.hidden = true;
  els.history.replaceChildren();
  document.body.classList.remove("is-intro");
  document.body.classList.add("is-playing");
  layout();
  game.queue = shuffle(playableKeys()).slice(0, game.length);
  beginRound();
}

function playableKeys() {
  const pairs = game.zone === "us" ? stateBorders : zonePairs[game.zone];
  const keys = pairs.map((pair) => pair.key);
  if (!mobileLayout.matches) return keys;
  const lookup = game.zone === "us" ? stateById : countryById;
  const visible = pairs.filter((pair) => {
    const left = lookup.get(pair.a);
    const right = lookup.get(pair.b);
    return left && right && pixelArea(left) >= 1400 && pixelArea(right) >= 1400;
  }).map((pair) => pair.key);
  return visible.length >= game.length ? visible : keys;
}

function pixelArea(unit) {
  const bounds = geoPath.bounds(unit.geometry);
  const width = bounds[1][0] - bounds[0][0];
  const height = bounds[1][1] - bounds[0][1];
  if (!Number.isFinite(width) || width <= 0 || height <= 0) return 0;
  return width * height;
}

function beginRound() {
  cancelResultReveal();
  hideNotes();
  resetMapView();
  const key = game.queue[game.index];
  const borders = game.zone === "us" ? stateBorders : countryBorders;
  const record = borders.find((border) => border.key === key);
  const lookup = game.zone === "us" ? stateById : countryById;
  const a = lookup.get(record.a);
  const b = lookup.get(record.b);
  game.pair = {
    key,
    a,
    b,
    geometry: {
      type: "MultiPolygon",
      coordinates: polygonParts(a).concat(polygonParts(b)),
    },
  };
  game.live = false;
  svg.classed("is-live", false).classed("is-settled", false);
  fusionPath.classed("is-hit", false);
  countryPaths.classed("is-miss", false).classed("is-fused", (unit) => unit.id === a.id || unit.id === b.id);
  statePaths.classed("is-miss", false).classed("is-fused", (unit) => unit.id === a.id || unit.id === b.id);
  borderPaths.classed("is-hidden", (border) => border.key === key);
  stateBorderPaths.classed("is-hidden", (border) => border.key === key);
  fusionPath.datum(game.pair.geometry).attr("display", null);
  layout();
  game.live = true;
  svg.classed("is-live", true);
  els.chrome.hidden = false;
  els.roundKicker.textContent = `Manche ${game.index + 1} / ${game.length}`;
  els.roundPrompt.textContent = "Alors ?";
  els.timerBlock.hidden = false;
  paintTimer(game.roundMs);
  startTimer();
}

function onMapClick(event) {
  if (performance.now() < blockMapClickUntil) return;
  if (!game.live || !game.pair) return;
  const target = event.target;
  const id = target.getAttribute && target.getAttribute("data-id");
  if (target.classList.contains("fusion") || id === game.pair.a.id || id === game.pair.b.id) {
    settle("hit");
    return;
  }
  if (!id || target.classList.contains("is-inert")) return;
  if (game.zone === "us" && !stateById.has(id)) return;
  settle("miss", id);
}

function findUnit(id) {
  return countryById.get(id) || stateById.get(id) || null;
}

function settle(outcome, missId) {
  if (!game.live) return;
  resetMapView();
  game.live = false;
  stopTimer();
  svg.classed("is-live", false).classed("is-settled", true);
  fusionPath.classed("is-hit", true);
  if (missId) {
    countryPaths.filter((unit) => unit.id === missId).classed("is-miss", true);
    statePaths.filter((unit) => unit.id === missId).classed("is-miss", true);
  }
  const missed = missId ? findUnit(missId) : null;
  const round = {
    a: game.pair.a,
    b: game.pair.b,
    outcome,
    label: pairLabel(game.pair.a, game.pair.b),
    miss: missed || null,
  };
  game.rounds.push(round);
  els.timerBlock.hidden = true;
  els.chrome.hidden = true;
  if (outcome === "timeout") {
    playVerdict(false);
    notesOpen = true;
    placeNotes();
    resultReveal = window.setTimeout(() => {
      resultReveal = 0;
      hideNotes();
      showResult(round);
      renderHistory();
    }, REVEAL_MS);
    return;
  }
  showResult(round);
  renderHistory();
  playVerdict(outcome === "hit");
}

function showResult(round) {
  document.body.classList.add("is-result");
  els.reviewBar.hidden = true;
  els.result.hidden = false;
  els.resultMark.textContent = round.outcome === "hit" ? "✅" : "❌";
  els.resultKicker.textContent = `Manche ${game.index + 1} / ${game.length}`;
  els.resultPrompt.textContent = outcomeLabel(round.outcome);
  els.resultLead.textContent = RESULT_LEAD[game.zone];
  els.resultLabel.textContent = round.label;
  els.btnNext.textContent = game.index + 1 >= game.length ? "Voir le score" : "Manche suivante";
}

function cancelResultReveal() {
  if (!resultReveal) return;
  window.clearTimeout(resultReveal);
  resultReveal = 0;
}

function showResultAgain() {
  hideNotes();
  document.body.classList.add("is-result");
  els.reviewBar.hidden = true;
  els.result.hidden = false;
}

function showMap() {
  clearVerdict();
  document.body.classList.remove("is-result");
  els.result.hidden = true;
  els.reviewBar.hidden = false;
  notesOpen = !!game.rounds[game.index];
  placeNotes();
}

function hideNotes() {
  notesOpen = false;
  els.notes.hidden = true;
}

function placeNotes() {
  if (!notesOpen) {
    els.notes.hidden = true;
    return;
  }
  const round = game.rounds[game.index];
  const fusionNode = fusionPath.node();
  if (!round || !fusionNode) return;
  const missPath = round.miss ? pathNode(round.miss.id) : null;
  els.noteFusionKicker.textContent = RESULT_LEAD[game.zone];
  els.noteFusionName.textContent = round.label;
  els.noteMiss.hidden = !missPath;
  if (missPath) els.noteMissName.textContent = round.miss.name;
  els.notes.hidden = false;

  const obstacles = [els.reviewBar, els.historyWrap]
    .filter((el) => el.getClientRects().length)
    .map((el) => el.getBoundingClientRect());
  obstacles.push(fusionNode.getBoundingClientRect());
  if (missPath) obstacles.push(missPath.getBoundingClientRect());
  const fusionAnchor = anchorOf(fusionNode);
  const fusionSize = { width: els.noteFusion.offsetWidth, height: els.noteFusion.offsetHeight };
  let fusion = chooseNoteSide(fusionAnchor, fusionSize, obstacles);
  if (!missPath) {
    applyNote(els.noteFusion, fusion);
    return;
  }
  const missAnchor = anchorOf(missPath);
  const missSize = { width: els.noteMiss.offsetWidth, height: els.noteMiss.offsetHeight };
  let miss = chooseNoteSide(missAnchor, missSize, obstacles);
  if (intersects(miss.rect, fusion.rect, 8)) {
    const flippedFusion = chooseNoteSide(fusionAnchor, fusionSize, obstacles, oppositeSide(fusion.side));
    if (!intersects(miss.rect, flippedFusion.rect, 8)) fusion = flippedFusion;
    else {
      const flippedMiss = chooseNoteSide(missAnchor, missSize, obstacles, oppositeSide(miss.side));
      if (!intersects(flippedMiss.rect, fusion.rect, 8)) miss = flippedMiss;
      else if (miss.rect.top <= fusion.rect.top) {
        const delta = miss.rect.bottom + 10 - fusion.rect.top;
        fusion = { side: fusion.side, rect: shiftRect(fusion.rect, delta) };
      } else {
        const delta = fusion.rect.bottom + 10 - miss.rect.top;
        miss = { side: miss.side, rect: shiftRect(miss.rect, delta) };
      }
    }
  }
  applyNote(els.noteMiss, miss);
  applyNote(els.noteFusion, fusion);
}

function pathNode(id) {
  const country = countryPaths.filter((unit) => unit.id === id).node();
  if (country && country.getAttribute("display") !== "none" && stateLayer.attr("display") !== "none") {
    const state = statePaths.filter((unit) => unit.id === id).node();
    if (state) return state;
  }
  if (game.zone === "us") {
    const state = statePaths.filter((unit) => unit.id === id).node();
    if (state) return state;
  }
  return country || statePaths.filter((unit) => unit.id === id).node();
}

function oppositeSide(side) {
  return side === "above" ? "below" : "above";
}

function anchorOf(node) {
  const rect = node.getBoundingClientRect();
  return {
    x: rect.left + rect.width / 2,
    top: rect.top,
    bottom: rect.bottom,
  };
}

function chooseNoteSide(anchor, size, obstacles, prefer = "above") {
  const order = prefer === "above" ? ["above", "below"] : ["below", "above"];
  for (const side of order) {
    const rect = noteRect(anchor, size, side);
    if (noteFits(rect, obstacles)) return { side, rect };
  }
  const side = anchor.top > window.innerHeight - anchor.bottom ? "above" : "below";
  return { side, rect: noteRect(anchor, size, side) };
}

function noteRect(anchor, size, side) {
  const margin = 10;
  const gap = 18;
  let left = anchor.x - size.width / 2;
  left = Math.max(margin, Math.min(left, window.innerWidth - margin - size.width));
  const top = side === "above" ? anchor.top - gap - size.height : anchor.bottom + gap;
  return {
    left,
    top,
    right: left + size.width,
    bottom: top + size.height,
    width: size.width,
    height: size.height,
    tip: Math.max(16, Math.min(size.width - 16, anchor.x - left)),
  };
}

function noteFits(rect, obstacles) {
  const margin = 10;
  if (rect.top < margin || rect.bottom > window.innerHeight - margin) return false;
  return !obstacles.some((box) => intersects(rect, box, 12));
}

function intersects(a, b, pad = 0) {
  return a.left < b.right + pad && a.right + pad > b.left && a.top < b.bottom + pad && a.bottom + pad > b.top;
}

function shiftRect(rect, dy) {
  return { ...rect, top: rect.top + dy, bottom: rect.bottom + dy };
}

function applyNote(note, placed) {
  note.classList.toggle("is-above", placed.side === "above");
  note.classList.toggle("is-below", placed.side === "below");
  note.style.left = `${placed.rect.left}px`;
  note.style.top = `${placed.rect.top}px`;
  note.style.setProperty("--tip", `${placed.rect.tip}px`);
}

function hideResult() {
  cancelResultReveal();
  hideNotes();
  document.body.classList.remove("is-result");
  els.result.hidden = true;
  els.reviewBar.hidden = true;
  clearVerdict();
}

function clearVerdict() {
  cancelAnimationFrame(verdictFrame);
  window.clearTimeout(verdictTimer);
  verdictFrame = 0;
  verdictTimer = 0;
  const canvas = els.verdict;
  const ctx = canvas.getContext("2d");
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, canvas.width, canvas.height);
}

function playVerdict(correct) {
  clearVerdict();
  const canvas = els.verdict;
  const reduce = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  const width = Math.max(1, window.innerWidth);
  const height = Math.max(1, window.innerHeight);
  const dpr = Math.min(2, window.devicePixelRatio || 1);
  canvas.width = Math.round(width * dpr);
  canvas.height = Math.round(height * dpr);
  canvas.style.left = "0px";
  canvas.style.top = "0px";
  canvas.style.width = `${width}px`;
  canvas.style.height = `${height}px`;
  const ctx = canvas.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const card = document.querySelector(".result-card");
  const cardRect = card ? card.getBoundingClientRect() : null;
  const originX = cardRect && cardRect.width > 1 ? cardRect.left + cardRect.width / 2 : width / 2;
  const originY = cardRect && cardRect.height > 1 ? cardRect.top + cardRect.height / 2 : height * 0.42;
  const colors = correct
    ? ["#c23b33", "#8d241e", "#1c1915", "#e4c56a"]
    : ["#c23b33", "#8d241e"];
  const pieces = [];
  const count = correct ? 86 : 26;
  for (let i = 0; i < count; i += 1) {
    const angle = correct
      ? Math.random() * Math.PI * 2
      : Math.PI * (0.15 + Math.random() * 0.7);
    const speed = correct ? 220 + Math.random() * 640 : 80 + Math.random() * 280;
    pieces.push({
      x: originX + (Math.random() - 0.5) * 24,
      y: originY + (Math.random() - 0.5) * 16,
      vx: Math.cos(angle) * speed,
      vy: Math.sin(angle) * speed - (correct ? 80 : 0),
      spin: Math.random() * Math.PI,
      spinV: (Math.random() - 0.5) * 10,
      size: correct ? 4 + Math.random() * 8 : 5 + Math.random() * 11,
      shape: Math.floor(Math.random() * 3),
      color: colors[Math.floor(Math.random() * colors.length)],
      drag: correct ? 0.985 : 0.97,
    });
  }
  const paintPiece = (piece) => {
    ctx.save();
    ctx.translate(piece.x, piece.y);
    ctx.rotate(piece.spin);
    ctx.fillStyle = piece.color;
    const s = piece.size;
    ctx.beginPath();
    if (!correct || piece.shape === 2) {
      ctx.arc(0, 0, s * 0.55, 0, Math.PI * 2);
    } else if (piece.shape === 0) {
      ctx.moveTo(0, -s);
      ctx.lineTo(s * 0.55, 0);
      ctx.lineTo(0, s);
      ctx.lineTo(-s * 0.55, 0);
      ctx.closePath();
    } else {
      for (let k = 0; k < 8; k += 1) {
        const a = (k / 8) * Math.PI * 2 - Math.PI / 2;
        const rad = k % 2 ? s * 0.38 : s;
        if (k === 0) ctx.moveTo(Math.cos(a) * rad, Math.sin(a) * rad);
        else ctx.lineTo(Math.cos(a) * rad, Math.sin(a) * rad);
      }
      ctx.closePath();
    }
    ctx.fill();
    ctx.restore();
  };
  const drawAt = (t) => {
    ctx.clearRect(0, 0, width, height);
    const flash = Math.max(0, 1 - t / 0.28);
    if (flash > 0) {
      ctx.fillStyle = correct
        ? `rgba(228, 197, 106, ${0.28 * flash})`
        : `rgba(194, 59, 51, ${0.16 * flash})`;
      ctx.fillRect(0, 0, width, height);
    }
    if (correct) {
      const ring = Math.min(1, t / 0.7);
      ctx.strokeStyle = `rgba(194, 59, 51, ${0.55 * (1 - ring)})`;
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc(originX, originY, 28 + ring * 260, 0, Math.PI * 2);
      ctx.stroke();
    }
    const fade = t < 1.05 ? 1 : Math.max(0, 1 - (t - 1.05) / 0.45);
    ctx.globalAlpha = fade;
    pieces.forEach((piece) => {
      paintPiece(piece);
      piece.x += piece.vx / 60;
      piece.y += piece.vy / 60;
      piece.vy += correct ? 28 : 18;
      piece.vx *= piece.drag;
      piece.spin += piece.spinV / 60;
    });
    ctx.globalAlpha = 1;
  };
  if (reduce) {
    drawAt(0.45);
    verdictTimer = window.setTimeout(clearVerdict, 700);
    return;
  }
  const started = performance.now();
  const tick = (now) => {
    const t = (now - started) / 1000;
    if (t >= 1.55) {
      clearVerdict();
      return;
    }
    drawAt(t);
    verdictFrame = requestAnimationFrame(tick);
  };
  verdictFrame = requestAnimationFrame(tick);
}

function onNext() {
  if (game.index + 1 >= game.length) {
    hideResult();
    showFinish();
    return;
  }
  game.index += 1;
  beginRound();
  hideResult();
}

function showFinish() {
  const score = game.rounds.filter((round) => round.outcome === "hit").length;
  els.finalScore.textContent = `${score} / ${game.length}`;
  els.finishRecap.replaceChildren();
  game.rounds.forEach((round) => {
    const item = document.createElement("li");
    const name = document.createElement("p");
    name.className = "finish-recap-name";
    name.textContent = round.label;
    const mark = document.createElement("p");
    mark.className = "finish-recap-score" + (round.outcome === "hit" ? "" : " is-miss");
    mark.textContent = outcomeLabel(round.outcome);
    item.append(name, mark);
    els.finishRecap.append(item);
  });
  els.chrome.hidden = true;
  els.historyWrap.hidden = true;
  els.timerBlock.hidden = true;
  els.finish.hidden = false;
}

function showIntro() {
  stopTimer();
  cancelResultReveal();
  resetMapView();
  game.live = false;
  game.pair = null;
  fusionPath.attr("display", "none").classed("is-hit", false);
  countryPaths.classed("is-miss", false).classed("is-fused", false);
  statePaths.classed("is-miss", false).classed("is-fused", false);
  borderPaths.classed("is-hidden", false);
  stateBorderPaths.classed("is-hidden", false);
  svg.classed("is-live", false).classed("is-settled", false);
  hideResult();
  els.finish.hidden = true;
  els.chrome.hidden = true;
  els.timerBlock.hidden = true;
  els.historyWrap.hidden = true;
  els.intro.hidden = false;
  document.body.classList.add("is-intro");
  document.body.classList.remove("is-playing");
  selectZone(selectedZone());
}

function renderHistory() {
  const total = game.rounds.filter((round) => round.outcome === "hit").length;
  els.history.replaceChildren();
  game.rounds.forEach((round) => {
    const item = document.createElement("li");
    const name = document.createElement("span");
    name.className = "pair-name";
    name.textContent = round.label;
    const score = document.createElement("span");
    score.className = "score-num" + (round.outcome === "hit" ? "" : " is-miss");
    score.textContent = round.outcome === "hit" ? "1" : "0";
    item.append(name, score);
    els.history.append(item);
  });
  const sum = document.createElement("li");
  sum.className = "score-history-total";
  const label = document.createElement("span");
  label.textContent = "Total";
  const value = document.createElement("span");
  value.className = "score-num";
  value.textContent = `${total} / ${game.length}`;
  sum.append(label, value);
  els.history.append(sum);
  els.historyWrap.hidden = false;
}

function startTimer() {
  stopTimer();
  const started = performance.now();
  const frame = (now) => {
    const left = game.roundMs - (now - started);
    if (left <= 0) {
      paintTimer(0);
      settle("timeout");
      return;
    }
    paintTimer(left);
    timerFrame = requestAnimationFrame(frame);
  };
  timerFrame = requestAnimationFrame(frame);
}

function stopTimer() {
  if (!timerFrame) return;
  cancelAnimationFrame(timerFrame);
  timerFrame = 0;
}

function onMapPointerDown(event) {
  if (!mobileLayout.matches || !game.live || event.pointerType === "mouse") return;
  mapPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
  try { mapNode.setPointerCapture(event.pointerId); } catch (error) { /* synthetic pointers */ }
  if (mapPointers.size === 2) beginMapPinch();
}

function onMapPointerMove(event) {
  if (!mapPointers.has(event.pointerId)) return;
  mapPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
  if (mapPointers.size < 2 || !mapPinch) return;
  event.preventDefault();
  moveMapPinch();
}

function onMapPointerEnd(event) {
  if (!mapPointers.has(event.pointerId)) return;
  mapPointers.delete(event.pointerId);
  if (mapPointers.size < 2) mapPinch = null;
}

function beginMapPinch() {
  const [a, b] = fingerPair();
  mapPinch = {
    dist: Math.max(1, fingerSpan(a, b)),
    midX: (a.x + b.x) / 2,
    midY: (a.y + b.y) / 2,
    scale: mapView.scale,
    x: mapView.x,
    y: mapView.y,
  };
  blockMapClickUntil = performance.now() + 700;
}

function moveMapPinch() {
  const [a, b] = fingerPair();
  const dist = Math.max(1, fingerSpan(a, b));
  const midX = (a.x + b.x) / 2;
  const midY = (a.y + b.y) / 2;
  const scale = clamp(mapPinch.scale * (dist / mapPinch.dist), 1, 6);
  const contentX = (mapPinch.midX - mapPinch.x) / mapPinch.scale;
  const contentY = (mapPinch.midY - mapPinch.y) / mapPinch.scale;
  mapView.scale = scale;
  mapView.x = midX - contentX * scale;
  mapView.y = midY - contentY * scale;
  if (mapView.scale === 1) {
    mapView.x = 0;
    mapView.y = 0;
  } else {
    clampMapPan();
  }
  applyMapView();
  blockMapClickUntil = performance.now() + 700;
}

function fingerPair() {
  return [...mapPointers.values()].slice(0, 2);
}

function fingerSpan(a, b) {
  return Math.hypot(a.x - b.x, a.y - b.y);
}

function clampMapPan() {
  const width = els.map.clientWidth;
  const height = els.map.clientHeight;
  const edge = 48;
  mapView.x = clamp(mapView.x, edge - width * mapView.scale, width - edge);
  mapView.y = clamp(mapView.y, edge - height * mapView.scale, height - edge);
}

function applyMapView() {
  if (mapView.scale === 1 && mapView.x === 0 && mapView.y === 0) {
    mapNode.style.transform = "";
    return;
  }
  mapNode.style.transformOrigin = "0 0";
  mapNode.style.transform = `translate(${mapView.x}px, ${mapView.y}px) scale(${mapView.scale})`;
}

function resetMapView() {
  mapView.scale = 1;
  mapView.x = 0;
  mapView.y = 0;
  mapPinch = null;
  mapPointers.clear();
  mapNode.style.transform = "";
}

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function paintTimer(left) {
  const ratio = Math.max(0, Math.min(1, left / game.roundMs));
  const shown = left <= 0 ? 0 : Math.ceil(left / 1000);
  els.timerFill.style.width = `${ratio * 100}%`;
  els.timerBar.setAttribute("aria-valuenow", String(Math.round(ratio * 100)));
  els.timerValue.textContent = `${shown} s`;
}

function layout() {
  if (!prepareView()) return;
  if (document.body.classList.contains("is-playing") || !placed) {
    stopGlobeSpin();
    fitProjection();
    drawMap();
    placed = true;
    if (document.body.classList.contains("is-playing")) placeNotes();
    return;
  }
  flyToFrame();
}

function prepareView() {
  const width = els.map.clientWidth;
  const height = els.map.clientHeight;
  if (!width || !height || !ready) return false;
  view.width = width;
  view.height = height;
  svg.attr("viewBox", `0 0 ${width} ${height}`);
  maskRect.attr("width", width).attr("height", height);
  const us = game.zone === "us";
  stateLayer.attr("display", us ? null : "none");
  stateBorderLayer.attr("display", us ? null : "none");
  countryPaths.classed("is-inert", () => us);
  return true;
}

function drawMap() {
  const sphere = geoPath({ type: "Sphere" });
  shadowPath.attr("d", sphere);
  spherePath.attr("d", sphere);
  countryPaths.attr("d", (unit) => geoPath(unit.geometry));
  statePaths.attr("d", (unit) => geoPath(unit.geometry));
  borderPaths.attr("d", (border) => geoPath(border.geometry));
  stateBorderPaths.attr("d", (border) => geoPath(border.geometry));
  lakeMaskPaths.attr("d", geoPath);
  lakePaths.attr("d", geoPath);
  coastPath.attr("d", geoPath(coast));
  if (game.pair) fusionPath.attr("d", geoPath(game.pair.geometry));
}

function stopGlobeSpin() {
  if (!globeSpin) return;
  globeSpin.stop();
  globeSpin = null;
}

function angleDelta(from, to) {
  return ((to - from + 540) % 360) - 180;
}

function flyToFrame() {
  if (!prepareView()) return;
  if (window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
    stopGlobeSpin();
    fitProjection();
    drawMap();
    return;
  }
  const box = activeFrame();
  stopGlobeSpin();
  const targetRotate = [-box.center[0], -box.center[1], 0];
  let fromRotate = projection.rotate();
  let fromScale = projection.scale();
  projection.rotate(targetRotate);
  const insets = viewInsets();
  const targetScale = frameScale(box, insets);
  const targetTranslate = [view.width / 2, insetCenterY(insets)];
  projection.rotate(fromRotate).scale(fromScale).translate(targetTranslate);
  const toLambda = fromRotate[0] + angleDelta(fromRotate[0], targetRotate[0]);
  const toPhi = fromRotate[1] + angleDelta(fromRotate[1], targetRotate[1]);
  const sweep = Math.max(Math.abs(toLambda - fromRotate[0]), Math.abs(toPhi - fromRotate[1]));
  if (sweep < 0.4 && Math.abs(targetScale - fromScale) < 2) {
    fitProjection();
    drawMap();
    return;
  }
  const duration = Math.round(Math.min(1800, 700 + sweep * 5));
  globeSpin = d3.timer((elapsed) => {
    const t = Math.min(1, elapsed / duration);
    const eased = d3.easeCubicInOut(t);
    projection.rotate([
      fromRotate[0] + (toLambda - fromRotate[0]) * eased,
      fromRotate[1] + (toPhi - fromRotate[1]) * eased,
      0,
    ]);
    projection.scale(fromScale + (targetScale - fromScale) * eased).translate(targetTranslate);
    drawMap();
    if (t === 1) stopGlobeSpin();
  });
}

function activeFrame() {
  const box = FRAMES[game.zone];
  if (!frameCompact.matches) return box;
  const centers = {
    europe: [18, 52],
    africa: [17, 0],
  };
  const center = centers[game.zone];
  return center ? { ...box, center } : box;
}

function fitProjection() {
  const box = activeFrame();
  const insets = viewInsets();
  projection.rotate([-box.center[0], -box.center[1]]);
  projection.scale(frameScale(box, insets)).translate([view.width / 2, insetCenterY(insets)]);
}

function safeInset(edge) {
  const key = "safe" + edge;
  if (view[key] != null) return view[key];
  const probe = document.createElement("div");
  probe.style.cssText = "position:fixed;left:0;visibility:hidden;pointer-events:none;height:env(safe-area-inset-" + edge + ")";
  document.body.append(probe);
  view[key] = probe.offsetHeight || 0;
  probe.remove();
  return view[key];
}

function viewInsets() {
  if (!frameCompact.matches) return { top: 48, right: 36, bottom: 32, left: 36 };
  return {
    top: 52 + safeInset("top"),
    right: 12,
    bottom: 20 + safeInset("bottom"),
    left: 12,
  };
}

function insetCenterY(insets) {
  return insets.top + (view.height - insets.top - insets.bottom) / 2;
}

function rectangleSamples(box) {
  const samples = [];
  for (let i = 0; i <= 6; i += 1) {
    for (let j = 0; j <= 4; j += 1) {
      samples.push([
        box.west + ((box.east - box.west) * i) / 6,
        box.south + ((box.north - box.south) * j) / 4,
      ]);
    }
  }
  return samples;
}

function mobileSamples(zone) {
  if (Object.prototype.hasOwnProperty.call(fitSamples, zone)) return fitSamples[zone];
  const points = [];
  const push = (unit, step, accept) => {
    if (!unit) return;
    polygonParts(unit).forEach((polygon) => {
      const ring = polygon[0];
      if (!ring) return;
      for (let i = 0; i < ring.length; i += step) {
        if (accept(ring[i])) points.push(ring[i]);
      }
    });
  };
  if (zone === "europe") {
    EUROPE.forEach((id) => {
      push(countryById.get(id), 5, (point) => point[0] >= -25 && point[0] <= 46 && point[1] >= 34 && point[1] <= 72);
    });
  } else if (zone === "africa") {
    AFRICA.forEach((id) => {
      push(countryById.get(id), 5, (point) => point[0] >= -19 && point[0] <= 53 && point[1] >= -35.2);
    });
  } else if (zone === "asia") {
    ASIA.forEach((id) => {
      push(countryById.get(id), 6, (point) => point[0] >= 25 && point[0] <= 150 && point[1] >= -12 && point[1] <= 66);
    });
  } else if (zone === "us") {
    states.forEach((state) => {
      if (US_SKIP.has(state.id)) return;
      push(state, 8, () => true);
    });
  }
  fitSamples[zone] = points.length ? points : null;
  return fitSamples[zone];
}

function frameScale(box, insets) {
  const outline = mobileSamples(game.zone);
  const samples = outline || rectangleSamples(box);
  const cx = view.width / 2;
  const cy = insetCenterY(insets);
  const fits = (scale) => {
    projection.scale(scale).translate([cx, cy]);
    return samples.every((sample) => {
      const point = projection(sample);
      if (!point) return true;
      return point[0] >= insets.left && point[0] <= view.width - insets.right
        && point[1] >= insets.top && point[1] <= view.height - insets.bottom;
    });
  };
  let lo = 40;
  let hi = 8000;
  if (!fits(lo)) return Math.min(view.width, view.height) * 0.46;
  while (hi - lo > 1) {
    const mid = (lo + hi) / 2;
    if (fits(mid)) lo = mid;
    else hi = mid;
  }
  return lo;
}

function polygonParts(feature) {
  const geometry = feature.geometry;
  if (!geometry) return [];
  if (geometry.type === "Polygon") return [geometry.coordinates];
  if (geometry.type === "MultiPolygon") return geometry.coordinates;
  return [];
}

function chainLines(lines) {
  const unused = new Set(lines.map((_, index) => index));
  const at = new Map();
  lines.forEach((line, index) => {
    [line[0], line[1]].forEach((point) => {
      const key = pointKey(point);
      const list = at.get(key);
      if (list) list.push(index);
      else at.set(key, [index]);
    });
  });
  const take = (key) => {
    const list = at.get(key);
    if (!list) return -1;
    for (let index = 0; index < list.length; index += 1) {
      if (unused.has(list[index])) return list[index];
    }
    return -1;
  };
  const chains = [];
  while (unused.size) {
    const first = unused.values().next().value;
    unused.delete(first);
    const chain = [lines[first][0].slice(), lines[first][1].slice()];
    [0, 1].forEach((end) => {
      let tip = end === 0 ? 0 : chain.length - 1;
      let next = take(pointKey(chain[tip]));
      while (next >= 0) {
        unused.delete(next);
        const line = lines[next];
        const tipKey = pointKey(chain[tip]);
        const point = pointKey(line[0]) === tipKey ? line[1] : line[0];
        if (end === 0) chain.unshift(point.slice());
        else chain.push(point.slice());
        tip = end === 0 ? 0 : chain.length - 1;
        next = take(pointKey(chain[tip]));
      }
    });
    chains.push(chain);
  }
  return chains;
}

function edgeKey(start, end) {
  const a = pointKey(start);
  const b = pointKey(end);
  if (a === b) return null;
  return a < b ? `${a}|${b}` : `${b}|${a}`;
}

function pointKey(point) {
  return `${Math.round(point[0] * 1000)},${Math.round(point[1] * 1000)}`;
}

function kmBetween(a, b) {
  const lon1 = (a[0] * Math.PI) / 180;
  const lat1 = (a[1] * Math.PI) / 180;
  const lon2 = (b[0] * Math.PI) / 180;
  const lat2 = (b[1] * Math.PI) / 180;
  const dlon = lon2 - lon1;
  const dlat = lat2 - lat1;
  const h = Math.sin(dlat / 2) ** 2 + Math.cos(lat1) * Math.cos(lat2) * Math.sin(dlon / 2) ** 2;
  return 2 * EARTH_KM * Math.asin(Math.min(1, Math.sqrt(h)));
}

function pairKey(idA, idB) {
  return [idA, idB].sort().join("|");
}

function pairLabel(a, b) {
  const [first, second] = [a.name, b.name].sort((left, right) => left.localeCompare(right, "fr"));
  return `${first} et ${second}`;
}

function outcomeLabel(outcome) {
  if (outcome === "hit") return "Bien vu";
  if (outcome === "timeout") return "Temps écoulé";
  return "Raté";
}

function shuffle(list) {
  const copy = list.slice();
  for (let i = copy.length - 1; i > 0; i -= 1) {
    const j = Math.floor(Math.random() * (i + 1));
    [copy[i], copy[j]] = [copy[j], copy[i]];
  }
  return copy;
}

function setProgress(value) {
  const shown = Math.max(0, Math.min(100, Math.round(value)));
  els.loadFill.style.width = `${shown}%`;
  els.loadBar.setAttribute("aria-valuenow", String(shown));
}

function nextFrame() {
  return new Promise((resolve) => {
    requestAnimationFrame(() => resolve());
  });
}
