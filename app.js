
const DB_NAME = "ammanabrolu-search-local";
const DB_VERSION = 1;
const STORE = "records";

let allRecords = [];
let filteredRecords = [];
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

function allowedEdits(n) {
  if (n <= 3) return 0;
  if (n === 4) return 1;
  if (n <= 11) return 2;
  return 3;
}

function editDistance(a, b) {
  a = compact(a); b = compact(b);
  const m = a.length, n = b.length;
  const d = Array.from({length: m + 1}, () => Array(n + 1).fill(0));
  for (let i = 0; i <= m; i++) d[i][0] = i;
  for (let j = 0; j <= n; j++) d[0][j] = j;
  for (let i = 1; i <= m; i++) {
    for (let j = 1; j <= n; j++) {
      const cost = a[i-1] === b[j-1] ? 0 : 1;
      d[i][j] = Math.min(
        d[i-1][j] + 1,
        d[i][j-1] + 1,
        d[i-1][j-1] + cost
      );
      if (i > 1 && j > 1 && a[i-1] === b[j-2] && a[i-2] === b[j-1]) {
        d[i][j] = Math.min(d[i][j], d[i-2][j-2] + cost);
      }
    }
  }
  return d[m][n];
}

function candidateUnits(name) {
  const tokens = norm(name).split(" ").filter(Boolean);
  const out = [];
  for (let i = 0; i < tokens.length; i++) {
    for (let size = 1; size <= Math.min(3, tokens.length - i); size++) {
      out.push(tokens.slice(i, i + size).join(""));
    }
  }
  if (tokens.length) out.push(tokens.join(""));
  return [...new Set(out)];
}

function closeUnit(query, unit) {
  const q = compact(query), u = compact(unit);
  if (!q || !u || q[0] !== u[0]) return false;
  const maxEdits = allowedEdits(q.length);
  if (u.length >= q.length) {
    if (editDistance(q, u.slice(0, q.length)) <= maxEdits) return true;
  }
  if (Math.abs(q.length - u.length) <= maxEdits) {
    if (editDistance(q, u) <= maxEdits) return true;
  }
  return false;
}

function closeNameMatch(query, candidate) {
  const qTokens = norm(query).split(" ").filter(Boolean);
  if (!qTokens.length) return true;
  const units = candidateUnits(candidate);
  return qTokens.every(q => units.some(u => closeUnit(q, u)));
}

function recordMatchesTerm(record, term) {
  const epic = compact(record.epic);
  const t = compact(term);
  if (t && epic === t) return true;

  return [
    record.name_en, record.name_te,
    record.relation_name_en, record.relation_name_te
  ].some(v => closeNameMatch(term, v || ""));
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
  $("statusLine").textContent = allRecords.length
    ? `${allRecords.length.toLocaleString()} private records loaded on this device`
    : "Private local data not loaded";
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

function applySearch() {
  const raw = $("query").value.trim();
  const terms = raw ? raw.split(/[,;\n]+/).map(x => x.trim()).filter(Boolean) : [];
  const part = $("partFilter").value;
  const gender = $("genderFilter").value;
  const ageMin = Number($("ageMin").value || 0);
  const ageMax = Number($("ageMax").value || 0);
  const address = norm($("addressFilter").value);

  filteredRecords = allRecords.filter(r => {
    if (part && String(r.part) !== part) return false;
    if (!genderMatch(r, gender)) return false;

    if (ageMin || ageMax) {
      const age = ageOf(r);
      if (age == null) return false;
      if (ageMin && age < ageMin) return false;
      if (ageMax && age > ageMax) return false;
    }

    if (address) {
      const addressFields = [
        r.house_en, r.house_te, r.section_en, r.section_te
      ].map(norm);
      if (!addressFields.some(v => v.includes(address))) return false;
    }

    if (!terms.length) return true;
    return terms.some(term => recordMatchesTerm(r, term));
  });

  renderResults();
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
  return [
    r.name_en || "",
    r.name_te || "",
    `ID: ${r.epic || ""}`,
    `Part: ${r.part ?? ""}`,
    `S.No: ${r.serial ?? ""}`,
    `Relation: ${r.relation_en || ""} / ${r.relation_te || ""}`,
    `Relation name: ${r.relation_name_en || ""} / ${r.relation_name_te || ""}`,
    `House: ${r.house_en || r.house_te || ""}`,
    `Age: ${r.age_en || r.age_te || ""}`,
    `Gender: ${r.gender_en || ""} / ${r.gender_te || ""}`,
    `Section: ${r.section_en || ""} / ${r.section_te || ""}`,
  ].join("\n");
}

function showDetail(r) {
  const box = $("detailContent");
  box.textContent = "";

  const purl = photoUrl(r);
  if (purl) {
    const img = document.createElement("img");
    img.src = purl;
    img.className = "detailPhoto";
    box.appendChild(img);
  }

  const en = document.createElement("div");
  en.className = "detailNameEn";
  en.textContent = r.name_en || "";
  const te = document.createElement("div");
  te.className = "detailNameTe";
  te.textContent = r.name_te || "";
  box.append(en, te);

  const grid = document.createElement("div");
  grid.className = "detailGrid";
  grid.append(
    detailItem("ID", r.epic),
    detailItem("Part", r.part),
    detailItem("Serial number", r.serial),
    detailItem("Relation", `${r.relation_en || ""} / ${r.relation_te || ""}`),
    detailItem("Relation name", `${r.relation_name_en || ""} / ${r.relation_name_te || ""}`),
    detailItem("House number", r.house_en || r.house_te),
    detailItem("Age", r.age_en || r.age_te),
    detailItem("Gender", `${r.gender_en || ""} / ${r.gender_te || ""}`),
    detailItem("Section", `${r.section_en || ""} / ${r.section_te || ""}`)
  );
  box.appendChild(grid);

  const buttons = document.createElement("div");
  buttons.className = "detailButtons";

  const copy = document.createElement("button");
  copy.textContent = "Copy details";
  copy.onclick = async () => {
    await navigator.clipboard.writeText(recordText(r));
    copy.textContent = "Copied";
    setTimeout(() => copy.textContent = "Copy details", 1200);
  };
  buttons.appendChild(copy);

  if (purl) {
    const open = document.createElement("button");
    open.textContent = "Open photo";
    open.onclick = () => window.open(purl, "_blank");
    buttons.appendChild(open);
  }

  box.appendChild(buttons);
  $("detailDialog").showModal();
}

function csvCell(v) {
  const s = String(v ?? "");
  return `"${s.replaceAll('"', '""')}"`;
}
function exportCsv() {
  if (!filteredRecords.length) return;
  const headers = [
    "Part","S.No","ID","Name English","Name Telugu",
    "Relation English","Relation Telugu",
    "Relation Name English","Relation Name Telugu",
    "House English","House Telugu","Age English","Age Telugu",
    "Gender English","Gender Telugu","Section English","Section Telugu"
  ];
  const rows = filteredRecords.map(r => [
    r.part,r.serial,r.epic,r.name_en,r.name_te,
    r.relation_en,r.relation_te,r.relation_name_en,r.relation_name_te,
    r.house_en,r.house_te,r.age_en,r.age_te,
    r.gender_en,r.gender_te,r.section_en,r.section_te
  ]);
  const csv = "\uFEFF" + [headers, ...rows].map(row => row.map(csvCell).join(",")).join("\r\n");
  const blob = new Blob([csv], {type:"text/csv;charset=utf-8"});
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = `ammanabrolu-search-${new Date().toISOString().slice(0,10)}.csv`;
  a.click();
  setTimeout(() => URL.revokeObjectURL(url), 2000);
}

async function importFile(file) {
  $("dataMessage").textContent = "Reading private file...";

  let records;

  if (file.name.toLowerCase().endsWith(".avdb")) {
    const buffer = await file.arrayBuffer();
    const zip = readStoredZip(buffer);
    const recordsBytes = zip.extract("records.json");
    const payload = JSON.parse(new TextDecoder("utf-8").decode(recordsBytes));

    if (payload.format !== "ammanabrolu-search-data-v2" || !Array.isArray(payload.records)) {
      throw new Error("This is not a compatible Ammanabrolu private data package.");
    }

    records = payload.records.map((r) => {
      const copy = {...r};
      if (copy.photo_file) {
        const bytes = zip.extract(copy.photo_file);
        copy.photo_blob = new Blob([bytes], {type: mimeFromName(copy.photo_file)});
      }
      delete copy.photo_file;
      return copy;
    });
  } else {
    // Backward compatibility with the earlier JSON test format.
    const rawText = await file.text();
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
    $("dataMessage").textContent = `Import failed: ${err.message}`;
  } finally {
    e.target.value = "";
  }
};

["query","addressFilter"].forEach(id => $(id).addEventListener("input", applySearch));
["partFilter","genderFilter","ageMin","ageMax"].forEach(id => $(id).addEventListener("change", applySearch));
$("clearFiltersBtn").onclick = () => {
  $("query").value = "";
  $("partFilter").value = "";
  $("genderFilter").value = "";
  $("ageMin").value = "";
  $("ageMax").value = "";
  $("addressFilter").value = "";
  applySearch();
};
$("exportBtn").onclick = exportCsv;
$("closeDialogBtn").onclick = () => $("detailDialog").close();

if ("serviceWorker" in navigator) {
  navigator.serviceWorker.register("./sw.js").catch(() => {});
}

loadLocalRecords().catch(err => {
  $("statusLine").textContent = "Local storage could not be opened";
  console.error(err);
});
