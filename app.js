
const DB_NAME = "ammanabrolu-search-local";
const DB_VERSION = 1;
const STORE = "records";

let allRecords = [];
let filteredRecords = [];
const matchedTermsById = new Map();
const photoUrlCache = new Map();

const $ = (id) => document.getElementById(id);

function revokePhotoUrls() {
  for (const url of photoUrlCache.values()) {
    try { URL.revokeObjectURL(url); } catch (_) {}
  }
  photoUrlCache.clear();
}

function photoUrl(record) {
  if (!record) return "";
  if (record.photo) return record.photo; // backward compatibility with old JSON format
  if (!record.photo_blob) return "";
  if (photoUrlCache.has(record.id)) return photoUrlCache.get(record.id);
  const url = URL.createObjectURL(record.photo_blob);
  photoUrlCache.set(record.id, url);
  return url;
}

function mimeFromName(name) {
  const n = (name || "").toLowerCase();
  if (n.endsWith(".png")) return "image/png";
  if (n.endsWith(".webp")) return "image/webp";
  if (n.endsWith(".gif")) return "image/gif";
  return "image/jpeg";
}

function readStoredZip(arrayBuffer) {
  const view = new DataView(arrayBuffer);
  const bytes = new Uint8Array(arrayBuffer);
  const decoder = new TextDecoder("utf-8");

  // Find End Of Central Directory (ZIP comment can be up to 65535 bytes).
  let eocd = -1;
  const min = Math.max(0, bytes.length - 65557);
  for (let i = bytes.length - 22; i >= min; i--) {
    if (view.getUint32(i, true) === 0x06054b50) { eocd = i; break; }
  }
  if (eocd < 0) throw new Error("Private data file is not a valid AVDB package.");

  const totalEntries = view.getUint16(eocd + 10, true);
  const centralOffset = view.getUint32(eocd + 16, true);
  const entries = new Map();
  let pos = centralOffset;

  for (let i = 0; i < totalEntries; i++) {
    if (view.getUint32(pos, true) !== 0x02014b50) {
      throw new Error("Private data package directory is damaged.");
    }
    const method = view.getUint16(pos + 10, true);
    const compressedSize = view.getUint32(pos + 20, true);
    const nameLen = view.getUint16(pos + 28, true);
    const extraLen = view.getUint16(pos + 30, true);
    const commentLen = view.getUint16(pos + 32, true);
    const localOffset = view.getUint32(pos + 42, true);
    const name = decoder.decode(bytes.slice(pos + 46, pos + 46 + nameLen));
    entries.set(name, { method, compressedSize, localOffset });
    pos += 46 + nameLen + extraLen + commentLen;
  }

  function extract(name) {
    const e = entries.get(name);
    if (!e) throw new Error(`Missing file inside private package: ${name}`);
    if (e.method !== 0) {
      throw new Error("This AVDB package uses compression not supported by this app version.");
    }
    const lo = e.localOffset;
    if (view.getUint32(lo, true) !== 0x04034b50) {
      throw new Error(`Damaged file entry: ${name}`);
    }
    const nameLen = view.getUint16(lo + 26, true);
    const extraLen = view.getUint16(lo + 28, true);
    const start = lo + 30 + nameLen + extraLen;
    return bytes.slice(start, start + e.compressedSize);
  }

  return { entries, extract };
}

function norm(value) {
  return (value ?? "")
    .toString()
    .normalize("NFKC")
    .toLocaleLowerCase()
    .replace(/[^\p{L}\p{N}]+/gu, " ")
    .trim()
    .replace(/\s+/g, " ");
}

function compact(value) { return norm(value).replace(/\s+/g, ""); }

function epicNorm(value) {
  return (value ?? "").toString().toUpperCase().replace(/[^A-Z0-9]/g, "");
}

function looksLikeEpic(value) {
  const raw = (value ?? "").toString().trim();
  const e = epicNorm(raw);
  return e.length >= 5 &&
    /[A-Z]/.test(e) &&
    /\d/.test(e) &&
    !/\s/.test(raw);
}

function splitSearchTerms(value) {
  const seen = new Set();
  const out = [];
  for (const part of (value || "").split(/[,;\n]+/)) {
    const p = part.trim().replace(/\s+/g, " ");
    if (!p) continue;
    const key = p.toLocaleLowerCase();
    if (!seen.has(key)) {
      seen.add(key);
      out.push(p);
    }
  }
  return out;
}

function allowedEdits(n) {
  if (n <= 3) return 0;
  if (n === 4) return 1;
  if (n <= 7) return 2;
  if (n <= 11) return 2;
  return 3;
}

// Damerau-Levenshtein distance, matching the Windows desktop app logic.
function editDistance(a, b) {
  a = compact(a); b = compact(b);
  const m = a.length, n = b.length;
  const d = Array.from({length: m + 1}, () => Array(n + 1).fill(0));
  for (let i = 0; i <= m; i++) d[i][0] = i;
  for (let j = 0; j <= n; j++) d[0][j] = j;

  for (let i = 1; i <= m; i++) {
    for (let j = 1; j <= n; j++) {
      const cost = a[i - 1] === b[j - 1] ? 0 : 1;
      d[i][j] = Math.min(
        d[i - 1][j] + 1,
        d[i][j - 1] + 1,
        d[i - 1][j - 1] + cost
      );
      if (
        i > 1 && j > 1 &&
        a[i - 1] === b[j - 2] &&
        a[i - 2] === b[j - 1]
      ) {
        d[i][j] = Math.min(d[i][j], d[i - 2][j - 2] + cost);
      }
    }
  }
  return d[m][n];
}

function candidateUnits(candidate) {
  const tokens = norm(candidate).split(" ").filter(Boolean);
  const units = [];

  for (let i = 0; i < tokens.length; i++) {
    for (let size = 1; size <= Math.min(3, tokens.length - i); size++) {
      units.push(tokens.slice(i, i + size).join(""));
    }
  }
  if (tokens.length) units.push(tokens.join(""));
  return [...new Set(units.filter(Boolean))];
}

function closeUnitScore(query, unit) {
  const q = compact(query), u = compact(unit);
  if (!q || !u) return 0;

  // Same conservative rule as the desktop app:
  // heri ~ hari, bharat ~ bharath; hari does not match ...chari.
  if (q[0] !== u[0]) return 0;

  const maxEdits = allowedEdits(q.length);

  if (u.length >= q.length) {
    const prefix = u.slice(0, q.length);
    const dist = editDistance(q, prefix);
    if (dist <= maxEdits) return 100 - dist * 8;
  }

  if (Math.abs(q.length - u.length) <= maxEdits) {
    const dist = editDistance(q, u);
    if (dist <= maxEdits) return 98 - dist * 8;
  }

  return 0;
}

function closeNameScore(query, candidate) {
  const qTokens = norm(query).split(" ").filter(Boolean);
  const cTokens = norm(candidate).split(" ").filter(Boolean);
  if (!qTokens.length || !cTokens.length) return 0;

  const units = candidateUnits(candidate);

  let compactPhraseScore = 0;
  for (const unit of units) {
    compactPhraseScore = Math.max(compactPhraseScore, closeUnitScore(query, unit));
  }

  const tokenScores = [];
  for (const qt of qTokens) {
    let best = 0;
    for (const unit of units) best = Math.max(best, closeUnitScore(qt, unit));
    if (best <= 0) return 0;
    tokenScores.push(best);
  }

  const avg = tokenScores.reduce((a, b) => a + b, 0) / tokenScores.length;
  return Math.max(avg, compactPhraseScore);
}

function wordExactMatch(query, candidate) {
  const qTokens = norm(query).split(" ").filter(Boolean);
  const cTokens = new Set(norm(candidate).split(" ").filter(Boolean));
  return qTokens.length > 0 && qTokens.every(t => cTokens.has(t));
}

function wordPrefixMatch(query, candidate) {
  const qTokens = norm(query).split(" ").filter(Boolean);
  const units = candidateUnits(candidate);
  if (!qTokens.length || !units.length) return false;

  return qTokens.every(qt => {
    const q = compact(qt);
    return units.some(unit => unit.startsWith(q));
  });
}

function searchValues(record, fieldKey) {
  if (fieldKey === "name") return [record.name_en, record.name_te];
  if (fieldKey === "relation") return [record.relation_name_en, record.relation_name_te];
  if (fieldKey === "house") return [record.house_en, record.house_te];
  if (fieldKey === "section") return [record.section_en, record.section_te];
  if (fieldKey === "address") {
    return [record.house_en, record.house_te, record.section_en, record.section_te];
  }
  if (fieldKey === "epic") return [record.epic];
  if (fieldKey === "serial") return [String(record.serial ?? "")];

  return [
    record.epic,
    String(record.serial ?? ""),
    record.name_en, record.name_te,
    record.relation_en, record.relation_te,
    record.relation_name_en, record.relation_name_te,
    record.house_en, record.house_te,
    record.section_en, record.section_te
  ];
}

function rowMatchScore(record, queryRaw, fieldKey, matchKey) {
  if (!(queryRaw || "").trim()) return 1;

  if (
    fieldKey === "epic" ||
    (fieldKey === "all" && looksLikeEpic(queryRaw))
  ) {
    const q = epicNorm(queryRaw);
    const e = epicNorm(record.epic);
    if (["normal", "exact", "word_exact", "approx"].includes(matchKey)) {
      return q === e ? 1000 : 0;
    }
    if (matchKey === "prefix") return e.startsWith(q) ? 950 : 0;
    if (matchKey === "contains") return q && e.includes(q) ? 950 : 0;
  }

  const q = norm(queryRaw);
  if (!q) return 0;

  const rawValues = searchValues(record, fieldKey);
  const values = rawValues
    .map(v => [String(v ?? ""), norm(v)])
    .filter(([, nv]) => nv);

  if (matchKey === "exact") {
    return values.some(([, nv]) => nv === q) ? 1000 : 0;
  }

  if (matchKey === "contains") {
    return values.some(([, nv]) => nv.includes(q)) ? 950 : 0;
  }

  if (matchKey === "word_exact") {
    return values.some(([raw]) => wordExactMatch(queryRaw, raw)) ? 970 : 0;
  }

  if (matchKey === "prefix") {
    return values.some(([raw]) => wordPrefixMatch(queryRaw, raw)) ? 960 : 0;
  }

  let fuzzyValues;
  if (fieldKey === "all") {
    // Matches desktop behavior: do not fuzzy-compare names with house/section/serial.
    fuzzyValues = [
      record.name_en, record.name_te,
      record.relation_name_en, record.relation_name_te
    ];
  } else {
    fuzzyValues = rawValues;
  }
  fuzzyValues = fuzzyValues.map(v => String(v ?? "")).filter(v => norm(v));

  if (matchKey === "approx") {
    let best = 0;
    const qCompact = compact(queryRaw);

    for (const candidate of fuzzyValues) {
      const units = candidateUnits(candidate);
      for (const unit of units) {
        if (!qCompact || !unit) continue;
        const allowance = allowedEdits(qCompact.length) + 1;

        if (unit.length >= qCompact.length) {
          const prefix = unit.slice(0, qCompact.length);
          const dist = editDistance(qCompact, prefix);
          if (dist <= allowance) best = Math.max(best, 100 - dist * 7);
        }

        if (Math.abs(unit.length - qCompact.length) <= allowance) {
          const dist = editDistance(qCompact, unit);
          if (dist <= allowance) best = Math.max(best, 98 - dist * 7);
        }
      }
    }

    return best >= 72 ? best : 0;
  }

  // NORMAL = desktop close-name / typo-tolerant mode.
  let best = 0;
  for (const candidate of fuzzyValues) {
    best = Math.max(best, closeNameScore(queryRaw, candidate));
  }
  return best > 0 ? 930 + best / 10 : 0;
}

function openDb() {
  return new Promise((resolve, reject) => {
    const req = indexedDB.open(DB_NAME, DB_VERSION);
    req.onupgradeneeded = () => {
      const db = req.result;
      if (!db.objectStoreNames.contains(STORE)) {
        db.createObjectStore(STORE, { keyPath: "id" });
      }
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
}

async function loadLocalRecords() {
  const db = await openDb();
  const tx = db.transaction(STORE, "readonly");
  const req = tx.objectStore(STORE).getAll();
  const data = await new Promise((resolve, reject) => {
    req.onsuccess = () => resolve(req.result || []);
    req.onerror = () => reject(req.error);
  });
  db.close();
  revokePhotoUrls();
  allRecords = data;
  updateStatus();
  applySearch();
}

async function replaceLocalRecords(records) {
  const db = await openDb();
  await new Promise((resolve, reject) => {
    const tx = db.transaction(STORE, "readwrite");
    const store = tx.objectStore(STORE);
    store.clear();
    records.forEach(r => store.put(r));
    tx.oncomplete = resolve;
    tx.onerror = () => reject(tx.error);
  });
  db.close();
  revokePhotoUrls();
  allRecords = records;
  updateStatus();
  applySearch();
}

async function removeLocalRecords() {
  await replaceLocalRecords([]);
  $("dataMessage").textContent = "Local private data removed from this device.";
}

function updateStatus() {
  if (!allRecords.length) {
    $("statusLine").textContent = "Private local data not loaded";
    return;
  }
  const photoCount = allRecords.reduce((n, r) => n + ((r.photo_blob || r.photo) ? 1 : 0), 0);
  $("statusLine").textContent =
    `${allRecords.length.toLocaleString()} records • ${photoCount.toLocaleString()} photos loaded locally`;
}

function ageOf(r) {
  const m = String(r.age_en ?? r.age_te ?? "").match(/\d{1,3}/);
  return m ? Number(m[0]) : null;
}

function genderMatch(r, wanted) {
  if (!wanted) return true;
  const en = norm(r.gender_en);
  const te = String(r.gender_te || "");
  if (wanted === "male") return (en.includes("male") && !en.includes("female")) || te.includes("పురుష");
  if (wanted === "female") return en.includes("female") || te.includes("స్త్రీ");
  return true;
}

function filterPasses(record) {
  const part = $("partFilter").value;
  const gender = $("genderFilter").value;
  const ageMin = Number($("ageMin").value || 0);
  const ageMax = Number($("ageMax").value || 0);
  const address = norm($("addressFilter").value);

  if (part && String(record.part) !== part) return false;
  if (!genderMatch(record, gender)) return false;

  if (ageMin || ageMax) {
    const age = ageOf(record);
    if (age == null) return false;
    if (ageMin && age < ageMin) return false;
    if (ageMax && age > ageMax) return false;
  }

  if (address) {
    const fields = [
      record.house_en, record.house_te,
      record.section_en, record.section_te
    ].map(norm);
    if (!fields.some(v => v.includes(address))) return false;
  }

  return true;
}

function applySearch() {
  try {
    const raw = $("query").value.trim();
    const fieldKey = $("searchField").value || "name";
    const matchKey = $("matchType").value || "normal";
    const multiKey = $("multiMode").value || "auto";

    const splitTerms = splitSearchTerms(raw);
    let effectiveMulti;
    let terms;

    if (multiKey === "auto") {
      if (splitTerms.length > 1) {
        effectiveMulti = "any";
        terms = splitTerms;
      } else {
        effectiveMulti = "single";
        terms = raw ? [raw] : [];
      }
    } else if (multiKey === "single") {
      effectiveMulti = "single";
      terms = raw ? [raw] : [];
    } else {
      effectiveMulti = multiKey;
      terms = splitTerms;
    }

    const scored = [];
    matchedTermsById.clear();

    for (const record of allRecords) {
      if (!filterPasses(record)) continue;

      let score = 1;
      let matched = [];

      if (terms.length) {
        const termScores = terms.map(term => [
          term,
          rowMatchScore(record, term, fieldKey, matchKey)
        ]);

        if (effectiveMulti === "all") {
          if (!termScores.every(([, s]) => s > 0)) continue;
          score = termScores.reduce((n, [, s]) => n + s, 0) / termScores.length;
          matched = termScores.filter(([, s]) => s > 0).map(([t]) => t);
        } else if (effectiveMulti === "any") {
          const positive = termScores.filter(([, s]) => s > 0);
          if (!positive.length) continue;
          score = Math.max(...positive.map(([, s]) => s));
          matched = positive.map(([t]) => t);
        } else {
          score = termScores[0][1];
          if (score <= 0) continue;
          matched = [termScores[0][0]];
        }
      }

      matchedTermsById.set(record.id, matched);
      scored.push({score, record});
    }

    scored.sort((a, b) =>
      (b.score - a.score) ||
      (Number(a.record.part || 0) - Number(b.record.part || 0)) ||
      (Number(a.record.serial || 0) - Number(b.record.serial || 0))
    );

    filteredRecords = scored.map(x => x.record);

    const modeText = [
      $("searchField").selectedOptions[0]?.text || "Voter name",
      $("matchType").selectedOptions[0]?.text || "Normal",
      effectiveMulti === "single"
        ? "single phrase"
        : `${effectiveMulti.toUpperCase()} comma mode`
    ].join(" • ");
    $("modeHint").textContent = modeText;

    renderResults();
  } catch (err) {
    console.error(err);
    $("resultCount").textContent = "SEARCH ERROR";
    $("modeHint").textContent = err.message || "Search failed";
  }
}

function renderResults() {
  $("resultCount").textContent = `${filteredRecords.length.toLocaleString()} results`;
  const holder = $("results");
  holder.textContent = "";

  if (!allRecords.length) {
    holder.innerHTML = '<div class="empty">Import your private local data to begin.</div>';
    return;
  }
  if (!filteredRecords.length) {
    holder.innerHTML = '<div class="empty">No matching record found.</div>';
    return;
  }

  const max = 150;
  filteredRecords.slice(0, max).forEach(r => {
    const node = $("cardTemplate").content.cloneNode(true);
    const card = node.querySelector(".card");
    const img = node.querySelector(".thumb");
    const purl = photoUrl(r);
    img.src = purl;
    img.style.visibility = purl ? "visible" : "hidden";
    node.querySelector(".nameEn").textContent = r.name_en || "";
    node.querySelector(".nameTe").textContent = r.name_te || "";
    node.querySelector(".meta").textContent =
      `${r.epic || ""}  •  Part ${r.part ?? ""}  •  S.No ${r.serial ?? ""}  •  House ${r.house_en || r.house_te || ""}  •  Age ${r.age_en || r.age_te || ""}`;

    const matched = matchedTermsById.get(r.id) || [];
    const matchedEl = node.querySelector(".matched");
    matchedEl.textContent = matched.length ? `Matched: ${matched.join(", ")}` : "";
    matchedEl.style.display = matched.length ? "block" : "none";

    card.addEventListener("click", () => showDetail(r));
    holder.appendChild(node);
  });

  if (filteredRecords.length > max) {
    const note = document.createElement("div");
    note.className = "empty";
    note.textContent = `Showing first ${max}. Export includes all ${filteredRecords.length.toLocaleString()} results.`;
    holder.appendChild(note);
  }
}

function detailItem(label, value) {
  const wrap = document.createElement("div");
  wrap.className = "detailItem";
  const l = document.createElement("div");
  l.className = "detailLabel";
  l.textContent = label;
  const v = document.createElement("div");
  v.className = "detailValue";
  v.textContent = value || "";
  wrap.append(l, v);
  return wrap;
}

function recordText(r) {
  const lines = [
    r.name_en || "",
    r.name_te || "",
    `EPIC: ${r.epic || ""}`,
    `Part / Booth: ${r.part ?? ""}`,
    `S.No: ${r.serial ?? ""}`,
    `Relation: ${r.relation_en || ""} / ${r.relation_te || ""}`,
    `Relation name: ${r.relation_name_en || ""} / ${r.relation_name_te || ""}`,
    `House: ${r.house_en || ""} / ${r.house_te || ""}`,
    `Age: ${r.age_en || ""} / ${r.age_te || ""}`,
    `Gender: ${r.gender_en || ""} / ${r.gender_te || ""}`,
    `Section: ${r.section_en || ""} / ${r.section_te || ""}`,
    `English PDF page: ${r.pdf_page_en || ""}`,
    `Telugu PDF page: ${r.pdf_page_te || ""}`
  ];

  if (r.authority_review) {
    lines.push(
      `AUTHORITY REVIEW: ${r.authority_field || ""}`,
      r.authority_note || ""
    );
  }
  return lines.join("\\n");
}

async function shareOrSavePhoto(r) {
  const blob = r.photo_blob;
  if (!blob) {
    const purl = photoUrl(r);
    if (purl) window.open(purl, "_blank");
    return;
  }

  const ext = blob.type?.includes("png") ? "png" : "jpg";
  const name = `${epicNorm(r.epic) || "photo"}.${ext}`;
  const file = new File([blob], name, {type: blob.type || "image/jpeg"});

  if (navigator.canShare && navigator.canShare({files:[file]})) {
    try {
      await navigator.share({files:[file], title: r.name_en || "Photo"});
      return;
    } catch (err) {
      if (err?.name === "AbortError") return;
    }
  }

  downloadBlob(blob, name);
}

function showThisHouse(r) {
  const house = r.house_en || r.house_te || "";
  if (!house) return;

  $("query").value = String(house);
  $("searchField").value = "house";
  $("matchType").value = "exact";
  $("multiMode").value = "single";
  $("partFilter").value = String(r.part ?? "");
  $("addressFilter").value = "";
  $("detailDialog").close();
  applySearch();
  window.scrollTo({top: 0, behavior: "smooth"});
}

function showDetail(r) {
  const box = $("detailContent");
  box.textContent = "";

  const purl = photoUrl(r);
  if (purl) {
    const img = document.createElement("img");
    img.src = purl;
    img.className = "detailPhoto";
    img.alt = r.name_en || "";
    box.appendChild(img);
  }

  const en = document.createElement("div");
  en.className = "detailNameEn";
  en.textContent = r.name_en || "";
  const te = document.createElement("div");
  te.className = "detailNameTe";
  te.textContent = r.name_te || "";
  box.append(en, te);

  if (r.authority_review) {
    const warn = document.createElement("div");
    warn.className = "authorityBox";
    warn.textContent =
      `AUTHORITY REVIEW — ${r.authority_field || ""}` +
      (r.authority_note ? `\\n${r.authority_note}` : "");
    box.appendChild(warn);
  }

  const grid = document.createElement("div");
  grid.className = "detailGrid";
  grid.append(
    detailItem("EPIC", r.epic),
    detailItem("Part / Booth", r.part),
    detailItem("Serial number", r.serial),
    detailItem("Relation", `${r.relation_en || ""} / ${r.relation_te || ""}`),
    detailItem("Relation name", `${r.relation_name_en || ""} / ${r.relation_name_te || ""}`),
    detailItem("House number", `${r.house_en || ""}${r.house_te && r.house_te !== r.house_en ? " / " + r.house_te : ""}`),
    detailItem("Age", `${r.age_en || ""}${r.age_te && r.age_te !== r.age_en ? " / " + r.age_te : ""}`),
    detailItem("Gender", `${r.gender_en || ""} / ${r.gender_te || ""}`),
    detailItem("Section", `${r.section_en || ""} / ${r.section_te || ""}`),
    detailItem("English PDF page", r.pdf_page_en),
    detailItem("Telugu PDF page", r.pdf_page_te)
  );
  box.appendChild(grid);

  const buttons = document.createElement("div");
  buttons.className = "detailButtons";

  const copy = document.createElement("button");
  copy.textContent = "Copy full record";
  copy.onclick = async () => {
    await navigator.clipboard.writeText(recordText(r));
    copy.textContent = "Copied";
    setTimeout(() => copy.textContent = "Copy full record", 1200);
  };
  buttons.appendChild(copy);

  if (purl) {
    const photoBtn = document.createElement("button");
    photoBtn.textContent = "Save / Share photo";
    photoBtn.onclick = () => shareOrSavePhoto(r);
    buttons.appendChild(photoBtn);

    const open = document.createElement("button");
    open.textContent = "Open photo";
    open.onclick = () => window.open(purl, "_blank");
    buttons.appendChild(open);
  }

  const house = document.createElement("button");
  house.textContent = "Show this house";
  house.onclick = () => showThisHouse(r);
  buttons.appendChild(house);

  box.appendChild(buttons);
  $("detailDialog").showModal();
}

function csvCell(v) {
  const s = String(v ?? "");
  return `"${s.replaceAll('"', '""')}"`;
}

function matchedInputText(r) {
  return (matchedTermsById.get(r.id) || []).join(", ");
}

function exportColumns() {
  return [
    ["Matched Input(s)", r => matchedInputText(r)],
    ["Part", r => r.part],
    ["S.No", r => r.serial],
    ["EPIC", r => r.epic],
    ["Voter Name English", r => r.name_en],
    ["Voter Name Telugu", r => r.name_te],
    ["Relation English", r => r.relation_en],
    ["Relation Telugu", r => r.relation_te],
    ["Relation Name English", r => r.relation_name_en],
    ["Relation Name Telugu", r => r.relation_name_te],
    ["House No English", r => r.house_en],
    ["House No Telugu", r => r.house_te],
    ["Age English", r => r.age_en],
    ["Age Telugu", r => r.age_te],
    ["Gender English", r => r.gender_en],
    ["Gender Telugu", r => r.gender_te],
    ["Section English", r => r.section_en],
    ["Section Telugu", r => r.section_te],
    ["English PDF Page", r => r.pdf_page_en],
    ["Telugu PDF Page", r => r.pdf_page_te],
    ["Authority Review", r => r.authority_review ? "YES" : ""],
    ["Authority Field", r => r.authority_field || ""],
    ["Authority Note", r => r.authority_note || ""],
    ["Photo Available", r => (r.photo_blob || r.photo) ? "YES" : ""]
  ];
}

function exportCsv() {
  if (!filteredRecords.length) return;

  const cols = exportColumns();
  const headers = cols.map(([name]) => name);
  const rows = filteredRecords.map(r => cols.map(([, getter]) => getter(r)));

  const csv =
    "\\uFEFF" +
    [headers, ...rows]
      .map(row => row.map(csvCell).join(","))
      .join("\\r\\n");

  const blob = new Blob([csv], {type:"text/csv;charset=utf-8"});
  downloadBlob(blob, `${exportBaseName()}.csv`);
}

function downloadBlob(blob, filename) {
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 5000);
}

function exportBaseName() {
  const d = new Date();
  const stamp = [
    d.getFullYear(),
    String(d.getMonth() + 1).padStart(2, "0"),
    String(d.getDate()).padStart(2, "0"),
    "_",
    String(d.getHours()).padStart(2, "0"),
    String(d.getMinutes()).padStart(2, "0")
  ].join("");
  return `ammanabrolu-search-${stamp}`;
}

function xmlEscape(value) {
  return String(value ?? "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&apos;");
}

function excelCol(n) {
  let s = "";
  while (n > 0) {
    n--;
    s = String.fromCharCode(65 + (n % 26)) + s;
    n = Math.floor(n / 26);
  }
  return s;
}

const CRC_TABLE = (() => {
  const table = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
    table[n] = c >>> 0;
  }
  return table;
})();

function crc32(bytes) {
  let c = 0xFFFFFFFF;
  for (let i = 0; i < bytes.length; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}

function le16(v) { return new Uint8Array([v & 255, (v >>> 8) & 255]); }
function le32(v) { return new Uint8Array([v & 255, (v >>> 8) & 255, (v >>> 16) & 255, (v >>> 24) & 255]); }
function cat(parts) {
  const len = parts.reduce((n, p) => n + p.length, 0);
  const out = new Uint8Array(len);
  let pos = 0;
  for (const p of parts) { out.set(p, pos); pos += p.length; }
  return out;
}

function dosDateTime() {
  const d = new Date();
  const time = ((d.getHours() & 31) << 11) | ((d.getMinutes() & 63) << 5) | ((Math.floor(d.getSeconds()/2)) & 31);
  const date = (((d.getFullYear()-1980) & 127) << 9) | (((d.getMonth()+1) & 15) << 5) | (d.getDate() & 31);
  return {time, date};
}

function makeZip(entries, mime) {
  const enc = new TextEncoder();
  const locals = [];
  const centrals = [];
  let offset = 0;
  const dt = dosDateTime();

  for (const e of entries) {
    const name = enc.encode(e.name);
    const data = e.data instanceof Uint8Array ? e.data : enc.encode(e.data);
    const crc = crc32(data);
    const flags = 0x0800;
    const local = cat([
      le32(0x04034b50), le16(20), le16(flags), le16(0), le16(dt.time), le16(dt.date),
      le32(crc), le32(data.length), le32(data.length), le16(name.length), le16(0), name, data
    ]);
    locals.push(local);

    const central = cat([
      le32(0x02014b50), le16(20), le16(20), le16(flags), le16(0), le16(dt.time), le16(dt.date),
      le32(crc), le32(data.length), le32(data.length), le16(name.length), le16(0), le16(0),
      le16(0), le16(0), le32(0), le32(offset), name
    ]);
    centrals.push(central);
    offset += local.length;
  }

  const centralSize = centrals.reduce((n, p) => n + p.length, 0);
  const eocd = cat([
    le32(0x06054b50), le16(0), le16(0), le16(entries.length), le16(entries.length),
    le32(centralSize), le32(offset), le16(0)
  ]);
  return new Blob([...locals, ...centrals, eocd], {type: mime});
}

function imageExtType(blob) {
  const type = (blob?.type || "image/jpeg").toLowerCase();
  if (type.includes("png")) return ["png", "image/png"];
  if (type.includes("webp")) return ["webp", "image/webp"];
  return ["jpg", "image/jpeg"];
}

async function buildXlsx(records, withPhotos) {
  const cols = exportColumns();
  const entries = [];
  const enc = new TextEncoder();
  const hasPhotos = withPhotos && records.some(r => r.photo_blob || r.photo);
  const startCol = hasPhotos ? 2 : 1;

  let headerCells = "";
  if (hasPhotos) headerCells += `<c r="A1" t="inlineStr" s="1"><is><t>Photo</t></is></c>`;
  cols.forEach(([name], i) => {
    const ref = `${excelCol(startCol + i)}1`;
    headerCells += `<c r="${ref}" t="inlineStr" s="1"><is><t>${xmlEscape(name)}</t></is></c>`;
  });

  const rowsXml = [`<row r="1" ht="24" customHeight="1">${headerCells}</row>`];
  const drawingAnchors = [];
  const drawingRels = [];
  const mediaEntries = [];
  let imageIndex = 0;

  for (let i = 0; i < records.length; i++) {
    const r = records[i];
    const excelRow = i + 2;
    let cells = "";
    if (hasPhotos) cells += `<c r="A${excelRow}" t="inlineStr"><is><t></t></is></c>`;
    cols.forEach(([, getter], j) => {
      const ref = `${excelCol(startCol + j)}${excelRow}`;
      cells += `<c r="${ref}" t="inlineStr"><is><t xml:space="preserve">${xmlEscape(getter(r) ?? "")}</t></is></c>`;
    });
    rowsXml.push(`<row r="${excelRow}"${hasPhotos ? ' ht="88" customHeight="1"' : ''}>${cells}</row>`);

    if (hasPhotos && r.photo_blob) {
      imageIndex++;
      const [ext] = imageExtType(r.photo_blob);
      const bytes = new Uint8Array(await r.photo_blob.arrayBuffer());
      mediaEntries.push({name:`xl/media/image${imageIndex}.${ext}`, data:bytes});
      drawingRels.push(`<Relationship Id="rId${imageIndex}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/image" Target="../media/image${imageIndex}.${ext}"/>`);
      drawingAnchors.push(`
        <xdr:oneCellAnchor>
          <xdr:from><xdr:col>0</xdr:col><xdr:colOff>36000</xdr:colOff><xdr:row>${excelRow-1}</xdr:row><xdr:rowOff>36000</xdr:rowOff></xdr:from>
          <xdr:ext cx="864000" cy="1080000"/>
          <xdr:pic>
            <xdr:nvPicPr><xdr:cNvPr id="${imageIndex}" name="Photo ${imageIndex}"/><xdr:cNvPicPr/></xdr:nvPicPr>
            <xdr:blipFill><a:blip r:embed="rId${imageIndex}"/><a:stretch><a:fillRect/></a:stretch></xdr:blipFill>
            <xdr:spPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="864000" cy="1080000"/></a:xfrm><a:prstGeom prst="rect"><a:avLst/></a:prstGeom></xdr:spPr>
          </xdr:pic>
          <xdr:clientData/>
        </xdr:oneCellAnchor>`);
    }

    if (i > 0 && i % 200 === 0) {
      $("exportMessage").textContent = `Preparing Excel... ${i.toLocaleString()} / ${records.length.toLocaleString()}`;
      await new Promise(requestAnimationFrame);
    }
  }

  const lastCol = excelCol(startCol + cols.length - 1);
  const columnsXml = hasPhotos
    ? `<cols><col min="1" max="1" width="13" customWidth="1"/><col min="2" max="${startCol + cols.length - 1}" width="18" customWidth="1"/></cols>`
    : `<cols><col min="1" max="${cols.length}" width="18" customWidth="1"/></cols>`;

  const drawingTag = hasPhotos && imageIndex ? `<drawing r:id="rId1"/>` : "";
  const sheetXml = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
  <worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">
    <dimension ref="A1:${lastCol}${records.length+1}"/>
    <sheetViews><sheetView workbookViewId="0"><pane ySplit="1" topLeftCell="A2" activePane="bottomLeft" state="frozen"/></sheetView></sheetViews>
    ${columnsXml}
    <sheetData>${rowsXml.join("")}</sheetData>
    <autoFilter ref="${hasPhotos ? 'B' : 'A'}1:${lastCol}${records.length+1}"/>
    ${drawingTag}
  </worksheet>`;

  const workbookXml = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets><sheet name="Search Results" sheetId="1" r:id="rId1"/></sheets></workbook>`;
  const workbookRels = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/><Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/></Relationships>`;
  const rootRels = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/></Relationships>`;
  const styles = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><fonts count="2"><font><sz val="10"/><name val="Arial"/></font><font><b/><color rgb="FFFFFFFF"/><sz val="10"/><name val="Arial"/></font></fonts><fills count="3"><fill><patternFill patternType="none"/></fill><fill><patternFill patternType="gray125"/></fill><fill><patternFill patternType="solid"><fgColor rgb="FF0F766E"/><bgColor indexed="64"/></patternFill></fill></fills><borders count="1"><border><left/><right/><top/><bottom/><diagonal/></border></borders><cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs><cellXfs count="2"><xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0"/><xf numFmtId="0" fontId="1" fillId="2" borderId="0" xfId="0" applyFont="1" applyFill="1"/></cellXfs><cellStyles count="1"><cellStyle name="Normal" xfId="0" builtinId="0"/></cellStyles></styleSheet>`;

  let contentTypes = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Default Extension="png" ContentType="image/png"/><Default Extension="jpg" ContentType="image/jpeg"/><Default Extension="jpeg" ContentType="image/jpeg"/><Default Extension="webp" ContentType="image/webp"/><Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/><Override PartName="/xl/worksheets/sheet1.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/><Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>`;
  if (hasPhotos && imageIndex) contentTypes += `<Override PartName="/xl/drawings/drawing1.xml" ContentType="application/vnd.openxmlformats-officedocument.drawing+xml"/>`;
  contentTypes += `</Types>`;

  entries.push({name:"[Content_Types].xml", data:contentTypes});
  entries.push({name:"_rels/.rels", data:rootRels});
  entries.push({name:"xl/workbook.xml", data:workbookXml});
  entries.push({name:"xl/_rels/workbook.xml.rels", data:workbookRels});
  entries.push({name:"xl/styles.xml", data:styles});
  entries.push({name:"xl/worksheets/sheet1.xml", data:sheetXml});

  if (hasPhotos && imageIndex) {
    const sheetRels = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/drawing" Target="../drawings/drawing1.xml"/></Relationships>`;
    const drawingXml = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><xdr:wsDr xmlns:xdr="http://schemas.openxmlformats.org/drawingml/2006/spreadsheetDrawing" xmlns:a="http://schemas.openxmlformats.org/drawingml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">${drawingAnchors.join("")}</xdr:wsDr>`;
    const drawingRelXml = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">${drawingRels.join("")}</Relationships>`;
    entries.push({name:"xl/worksheets/_rels/sheet1.xml.rels", data:sheetRels});
    entries.push({name:"xl/drawings/drawing1.xml", data:drawingXml});
    entries.push({name:"xl/drawings/_rels/drawing1.xml.rels", data:drawingRelXml});
    entries.push(...mediaEntries);
  }

  return makeZip(entries, "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet");
}

async function exportXlsx(withPhotos) {
  if (!filteredRecords.length) return;
  if (withPhotos && filteredRecords.length > 600) {
    const ok = confirm(`This export has ${filteredRecords.length.toLocaleString()} voters with photos. On an iPhone, very large photo Excel files can take time or use a lot of memory. Continue?`);
    if (!ok) return;
  }
  try {
    $("exportMessage").textContent = withPhotos ? "Preparing Excel with photos..." : "Preparing Excel...";
    const blob = await buildXlsx(filteredRecords, withPhotos);
    downloadBlob(blob, `${exportBaseName()}${withPhotos ? '-with-photos' : ''}.xlsx`);
    $("exportMessage").textContent = `Excel ready: ${filteredRecords.length.toLocaleString()} records${withPhotos ? ' with photos' : ''}.`;
  } catch (err) {
    console.error(err);
    $("exportMessage").textContent = `Excel export failed: ${err.message}`;
  }
}

function printableRecordHtml(r, withPhotos) {
  const purl = withPhotos ? photoUrl(r) : "";
  const auth = r.authority_review
    ? `<div class="auth">AUTH REVIEW: ${xmlEscape(r.authority_field || "")}</div>`
    : "";

  return `<article class="voter ${withPhotos ? 'withPhoto' : 'noPhoto'}">
    ${purl ? `<img src="${purl}" alt="">` : ''}
    <div class="vtext">
      ${auth}
      <div class="nen">${xmlEscape(r.name_en || '')}</div>
      <div class="nte">${xmlEscape(r.name_te || '')}</div>
      <div class="line"><b>EPIC:</b> ${xmlEscape(r.epic || '')} &nbsp; <b>Part:</b> ${xmlEscape(r.part ?? '')} &nbsp; <b>S.No:</b> ${xmlEscape(r.serial ?? '')}</div>
      <div class="line"><b>House:</b> ${xmlEscape(r.house_en || r.house_te || '')} &nbsp; <b>Age:</b> ${xmlEscape(r.age_en || r.age_te || '')} &nbsp; <b>Gender:</b> ${xmlEscape(r.gender_en || r.gender_te || '')}</div>
      <div class="line"><b>${xmlEscape(r.relation_en || 'Relation')}:</b> ${xmlEscape(r.relation_name_en || '')}</div>
      <div class="tel">${xmlEscape(r.relation_name_te || '')}</div>
      <div class="section">${xmlEscape(r.section_en || '')}${r.section_te ? ' / ' + xmlEscape(r.section_te) : ''}</div>
    </div>
  </article>`;
}

function currentCriteriaText() {
  const parts = [];

  if ($("query").value.trim()) parts.push(`Search: ${$("query").value.trim()}`);
  parts.push(`Search in: ${$("searchField").selectedOptions[0]?.text || ""}`);
  parts.push(`Match: ${$("matchType").selectedOptions[0]?.text || ""}`);
  parts.push(`Comma: ${$("multiMode").selectedOptions[0]?.text || ""}`);

  if ($("partFilter").value) parts.push(`Part: ${$("partFilter").value}`);
  if ($("genderFilter").value) parts.push(`Gender: ${$("genderFilter").value}`);

  if ($("ageMin").value || $("ageMax").value) {
    parts.push(`Age: ${$("ageMin").value || "Any"}-${$("ageMax").value || "Any"}`);
  }

  if ($("addressFilter").value.trim()) {
    parts.push(`House/section: ${$("addressFilter").value.trim()}`);
  }

  return parts.join(" | ") || "All matching records";
}

function exportPdf(withPhotos) {
  if (!filteredRecords.length) return;
  if (withPhotos && filteredRecords.length > 500) {
    const ok = confirm(`This will prepare ${filteredRecords.length.toLocaleString()} voters with photos for an A4 PDF. Large photo PDFs can be heavy on an iPhone. Continue?`);
    if (!ok) return;
  }

  const w = window.open("", "_blank");
  if (!w) {
    alert("Please allow the app to open the print preview window.");
    return;
  }

  const cards = filteredRecords.map(r => printableRecordHtml(r, withPhotos)).join("");
  const html = `<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Ammanabrolu Search PDF</title>
  <style>
    @page { size: A4 portrait; margin: 7mm; }
    * { box-sizing: border-box; }
    body { margin:0; font-family:-apple-system,BlinkMacSystemFont,"Noto Sans Telugu","Nirmala UI",Arial,sans-serif; color:#111; background:white; }
    .screenNote { padding:10px; background:#eef6ff; border-bottom:1px solid #b8d7f2; font-size:14px; }
    header { margin-bottom:4mm; border-bottom:1px solid #999; padding-bottom:2mm; }
    h1 { font-size:13pt; margin:0 0 1mm; }
    .criteria { font-size:7.5pt; color:#555; }
    .grid { display:grid; grid-template-columns:1fr 1fr; gap:2.6mm 3mm; align-items:start; }
    .voter { border:0.3mm solid #bbb; border-radius:1.4mm; padding:1.5mm; break-inside:avoid; page-break-inside:avoid; display:flex; gap:1.7mm; min-height:${withPhotos ? '33mm' : '21mm'}; }
    .voter img { width:24mm; height:30mm; object-fit:contain; background:#f2f2f2; border:0.25mm solid #aaa; flex:0 0 auto; }
    .vtext { min-width:0; flex:1; }
    .nen { font-size:8pt; font-weight:700; line-height:1.15; }
    .nte { font-size:8.3pt; font-weight:700; line-height:1.2; margin-top:0.7mm; }
    .line,.tel,.section { font-size:6.3pt; line-height:1.25; margin-top:0.7mm; overflow-wrap:anywhere; }
    .section { color:#555; }
    .auth { display:inline-block; font-size:5.6pt; font-weight:700; color:#755600; background:#fff3cd; border:0.2mm solid #d6a800; border-radius:0.8mm; padding:0.4mm 0.8mm; margin-bottom:0.6mm; }
    @media print { .screenNote { display:none; } }
  </style></head><body>
  <div class="screenNote"><b>To save as PDF on iPhone:</b> in the print preview, tap Share and choose Save to Files.</div>
  <header><h1>AMMANABROLU SEARCH - RESULTS</h1><div class="criteria">${xmlEscape(currentCriteriaText())} | ${filteredRecords.length.toLocaleString()} records</div></header>
  <main class="grid">${cards}</main>
  <script>
    window.addEventListener('load', () => {
      const imgs=[...document.images];
      Promise.all(imgs.map(img => img.complete ? Promise.resolve() : new Promise(res => { img.onload=res; img.onerror=res; }))).then(() => setTimeout(() => window.print(), 400));
    });
  <\/script></body></html>`;
  w.document.open();
  w.document.write(html);
  w.document.close();
}

async function importFile(file) {
  $("dataMessage").textContent =
    `Reading ${file.name} (${(file.size / 1024 / 1024).toFixed(1)} MB)...`;

  let records;

  // Do not rely on the filename extension. iPhone may treat a custom .avdb
  // extension as an unknown file type. Detect the ZIP package from its bytes.
  const buffer = await file.arrayBuffer();
  const sig = new Uint8Array(buffer, 0, Math.min(4, buffer.byteLength));
  const isZip =
    sig.length >= 4 &&
    sig[0] === 0x50 && sig[1] === 0x4B &&
    sig[2] === 0x03 && sig[3] === 0x04;

  if (isZip) {
    const zip = readStoredZip(buffer);
    const recordsBytes = zip.extract("records.json");
    const payload = JSON.parse(new TextDecoder("utf-8").decode(recordsBytes));

    if (payload.format !== "ammanabrolu-search-data-v2" || !Array.isArray(payload.records)) {
      throw new Error("This is not a compatible Ammanabrolu private data package.");
    }

    records = payload.records.map((r, i) => {
      const copy = {...r};
      if (copy.photo_file) {
        const bytes = zip.extract(copy.photo_file);
        copy.photo_blob = new Blob([bytes], {type: mimeFromName(copy.photo_file)});
      }
      delete copy.photo_file;

      if (i > 0 && i % 500 === 0) {
        $("dataMessage").textContent =
          `Preparing private records and photos... ${i.toLocaleString()} / ${payload.records.length.toLocaleString()}`;
      }
      return copy;
    });
  } else {
    // Backward compatibility with the earlier JSON test format.
    const rawText = new TextDecoder("utf-8").decode(new Uint8Array(buffer));
    const payload = JSON.parse(rawText);
    if (payload.format !== "ammanabrolu-search-data-v1" || !Array.isArray(payload.records)) {
      throw new Error("This is not a compatible private data file.");
    }
    records = payload.records;
  }

  if (!confirm(`Import ${records.length.toLocaleString()} private records onto this device?`)) {
    return;
  }

  $("dataMessage").textContent = "Saving records and photos locally on this iPhone...";
  await replaceLocalRecords(records);
  $("dataMessage").textContent =
    `Imported ${records.length.toLocaleString()} records locally on this device.`;
}


$("dataBtn").onclick = () => $("dataPanel").classList.toggle("hidden");
$("clearDataBtn").onclick = async () => {
  if (confirm("Remove the imported private data from this device?")) await removeLocalRecords();
};
$("fileInput").onchange = async (e) => {
  const file = e.target.files?.[0];
  if (!file) return;
  try { await importFile(file); }
  catch (err) {
    $("dataMessage").textContent = `Import failed: ${err.message}`; console.error(err);
  } finally {
    e.target.value = "";
  }
};

let searchTimer = null;
function scheduleSearch() {
  clearTimeout(searchTimer);
  searchTimer = setTimeout(applySearch, 180);
}

["query","addressFilter"].forEach(id => $(id).addEventListener("input", scheduleSearch));
[
  "searchField","matchType","multiMode",
  "partFilter","genderFilter","ageMin","ageMax"
].forEach(id => $(id).addEventListener("change", applySearch));

$("searchBtn").onclick = applySearch;

$("clearFiltersBtn").onclick = () => {
  $("query").value = "";
  $("searchField").value = "name";
  $("matchType").value = "normal";
  $("multiMode").value = "auto";
  $("partFilter").value = "";
  $("genderFilter").value = "";
  $("ageMin").value = "";
  $("ageMax").value = "";
  $("addressFilter").value = "";
  applySearch();
};

$("exportBtn").onclick = () => $("exportDialog").showModal();
$("closeExportBtn").onclick = () => $("exportDialog").close();
$("exportCsvBtn").onclick = exportCsv;
$("exportXlsxBtn").onclick = () => exportXlsx(false);
$("exportXlsxPhotosBtn").onclick = () => exportXlsx(true);
$("exportPdfBtn").onclick = () => exportPdf(false);
$("exportPdfPhotosBtn").onclick = () => exportPdf(true);
$("closeDialogBtn").onclick = () => $("detailDialog").close();

if ("serviceWorker" in navigator) {
  navigator.serviceWorker.register("./sw.js").catch(() => {});
}

loadLocalRecords().catch(err => {
  $("statusLine").textContent = "Local storage could not be opened";
  console.error(err);
});
