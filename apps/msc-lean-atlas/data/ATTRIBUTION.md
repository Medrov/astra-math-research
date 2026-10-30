# MSC2020 dataset attribution

The original classification is **MSC2020 — Mathematics Subject Classification**,
jointly maintained and published by **Mathematical Reviews (American Mathematical
Society) and zbMATH**.

- Official description and downloads: <https://msc2020.org/>
- Preserved CSV export: <https://msc2020.org/MSC_2020.csv>
- Preserved TeX export: <https://msc2020.org/MSC_2020.tex>
- License stated by the publisher: **Creative Commons Attribution–NonCommercial–
  ShareAlike 4.0 International**, <https://creativecommons.org/licenses/by-nc-sa/4.0/>.

The dataset files `MSC_2020.csv`, `MSC_2020.tex`, and the derived `msc2020.json`
retain this license. This notice concerns the classification data; it does not
assign a license to unrelated application code or Lean libraries.

Changes made by the SHAIM project: normalized identifiers, derived hierarchical
edges, typed explicit classification references, and expanded explicit ranges and
non-contextual suffix rules to existing categories. Source wording and source
files are retained. No mathematical theorem or equivalence is asserted by a
classification edge. No endorsement by the original publishers is implied.

`source-metadata.json` records retrieval timestamps and SHA-256 hashes. The CSV is
tab-separated Windows-1252 despite its extension. All 6603 CSV codes exactly match
the 6603 labels in the official TeX. These downloaded files have 63 root sections,
534 groups and 6006 terminal codes; the introductory web page's counts differ.
No nodes were invented to force agreement with those introductory totals.
