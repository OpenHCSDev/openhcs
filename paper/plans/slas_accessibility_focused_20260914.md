# SLAS accessibility: four approved follow-up edits

## Reading copy and scope

- [Updated manuscript PDF](../review/slas-accessibility-focused-20260914/manuscript.pdf)
- [Updated manuscript DOCX](../review/slas-accessibility-focused-20260914/manuscript.docx)
- [Unchanged supplementary PDF](../review/slas-accessibility-revision-20260914/author-copy/supplement.pdf)
- [Previous author copy](../review/slas-accessibility-revision-20260914/author-copy/manuscript.pdf)

The narrative audience is a biology PI without a software-specialist background;
the precision constraint is the SLAS Technology readership. The papers
repository's `paper-style-guide-pass` skill and canonical writing guide informed
the changes: concrete actions before terminology, replace dense explanation
rather than append it, and inspect the built pages. No verified numerical venue
page limit is assumed. The existing abstract is unchanged.

This pass implements the four follow-up changes approved after the accessibility
panel. It does not rerun analyses or add a new reviewer panel. The frozen
OpenHCS 0.8.5 result remains 30 executions, 25 selected-value comparisons and
two image-selected workflows. New reference-export/CI work is separate.

## Edit ledger

| Location | Reader's first recoverable claim | Unresolved entry state | Pointer load | Missing or weakened landing | Smallest repair | Audience encountering friction |
| --- | --- | --- | --- | --- | --- | --- |
| Figure 2, page 12 | Controls and Python show matching parameter values. | Full controls contain too much empty input width at publication size. | Full window, details and caption. | The values need zooming to compare. | Keep the full main window; crop control labels/values and the complete code-pattern block more tightly. Retain native pixels and capture checksums. | broad |
| Figure 3, page 14 | The recorded result includes outlines and path measurements. | A half-width table makes native column names and values too small. | Original inputs, video frame and details. | The table is visible without being comfortably readable. | Place the full video frame beside its outline detail and give the table the bottom row across the figure. Increase manuscript width from 5.5 to 6 inches. Preserve all five displayed rows, source pixels and calibration scope. | both |
| Authoring Results, page 11, and Figure 2 caption | Applying edited Python updates controls; editing a field regenerates Python. | Reading code can be confused with applying it; a field edit might be mistaken for a human mouse action. | Figure 2 and retained round-trip record. | The action causing each change was indirect. | Name the MCP code-application request and subsequent MCP field-edit request. Preserve the 99.8 to 99.6 to 99.8 sequence. Shorten the caption to keep it on the figure page. | both |
| Source-mapping Methods, page 5 | The workflow selects a nuclear channel, chooses how to process its planes and retains image identity. | Several configuration concepts arrive together. | Existing nuclear example; no new pointer. | The configuration choices are hard to picture. | Reuse the nuclear-segmentation example. Separate source selection from step-controlled stacking/grouping, then explain linked measurements and acquisition identity separately from storage. | broad |
| Performance Methods, page 10, and Results, page 17 | Worker count and queue depth are varied in separate experiments. | Fixed and varied conditions must be reconstructed from prose. | Table 2, Figure 5 and Supplementary Data 3. | The experiment design is difficult to scan. | Add a two-row fixed/varied design table; keep execution timing and output policy together below it. Keep the serial CellProfiler projection wholly supplementary. | both |

## Source checks

- Figure 2 still uses the verified same-session main-window, function-control
  and code captures and the recorded MCP round trip. The generators validate
  their original checksums. New control crop: `(25, 153, 193, 290)`; code crop:
  `(74, 96, 292, 222)`. The full main-window capture remains in panel A.
- Figure 3 still uses the original two full 800 x 800 TIFF images and the full
  frame at 600 seconds from the original OpenHCS 0.7.13 video. Detail crop
  coordinates are unchanged. Its rows remain path measurements, not one row
  per neuron. No crossover location, corrected image or physical calibration
  was invented.
- Table 2 was checked against the saved CSVs consumed by
  `build_slas_benchmark.load_tables()`. Throughput uses 2, 3 and 4 workers,
  with four assignments per worker. Memory combines the four-worker rows
  from the queue-depth files and core-scaling file: 1, 2, 3, 4, 6 and 8
  assignments per worker. All 30 workflows are present at each condition.
- No reference tree, benchmark manifest, comparison code or measurement CSV
  was modified. Only Figures 2 and 3 were regenerated in this follow-up.

## Build and verification

The canonical Markdown was built with `paper/build_docx_from_markdown.py` and
converted using headless LibreOffice with an isolated temporary profile.

- Main PDF remains **25 pages**. Figure 2 and its complete caption fit page 12;
  Figure 3 and its caption fit page 14. Table 2 fits page 10. Discussion and
  conclusion still finish on page 20; references finish on page 25.
- Compared extracted text through the full PDF against the previous author
  copy. Text changed only on pages 5, 6, 10, 11, 12, 17 and 21. Abstract,
  Discussion/conclusion and reference-page text are unchanged.
- Visually inspected the changed and reflowed pages, both figure pages,
  Discussion/conclusion and the final reference page. The initial build split
  the Figure 2 caption; shortening that caption resolved the split without
  shrinking its enlarged details or increasing the page count.
- All six embedded DOCX figures match the current PNG checksums; image
  paragraphs retain the caption-attachment setting. Both tables are present.
- Revalidated the Figure 2/3 receipts against every recorded source and output
  checksum. Both edited generators parse successfully; edited source files
  pass `git diff --check`.
- Earlier panel PDFs and author-copy baseline were preserved. Temporary
  render images and the private LibreOffice profile were removed after review.

Final PDF SHA256:
`f0b06b17016086e1c9b87e1aec74a6cd10310416a5174e98a8a103498baaea6e`

Final DOCX SHA256:
`6238cfdb9cac507ebbe703fd4c115894172eaa918164ad8237abdd0612d8051f`
