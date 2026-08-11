# ammanabrolu-search

Offline local search app shell.

This public repository contains only the application shell. Private records and
photos are imported separately and remain in local device storage.

## v5 — Desktop feature parity

The iPhone/PWA search now has the same main search choices as the Windows app:

### Search in
- Voter name
- All fields
- Relation name
- House number
- Section / area
- House + section
- EPIC
- Serial number

### Match type
- Normal — close name / typo tolerant
- Exact word(s) only
- Starts with input
- Approximate / fuzzy
- Contains letters anywhere
- Exact full field

### Multiple-input / comma modes
- AUTO — comma means ANY
- ANY item
- ALL items
- Treat as one phrase

### Filters
- Booth / Part
- Gender
- Age from
- Age to
- Independent House / section filter

### Result/detail tools
- Ranked results
- Shows which input term matched
- Copy full record
- Save / Share photo
- Open photo
- Show this house
- Authority-review warning
- Source PDF page numbers

### Export choices
- CSV — data only
- Excel — data only
- Excel — with photos
- PDF — no photos
- PDF — with photos

Exports include all matching records, not just the limited number displayed on
screen. Export columns include matched input(s), source PDF page numbers,
authority-review fields, and photo availability.

No private data is included in this repository.
