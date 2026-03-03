# Paper 4 ToC Readability Plan for Expert Review

## Context

Fritz and Wolpert both engaged substantively with the project. Neither response rejected the formal program outright. The immediate blocker is readability and theorem presentation, especially on the first page of the `paper4_toc` version.

## External Feedback

### Fritz

- The abstract introduces symbols before explaining them.
- The opening reads too much like formal output and not enough like prose for a human reader.
- The early theorem statements are hard to parse.
- The first theorem, as written in English, invited a mathematical objection.

### Wolpert

- The main correction was at the physics calibration layer.
- The issue was not a rejection of the combinatorial core.
- The practical consequence is that the paper must distinguish structural mathematics from empirical calibration more clearly.

## Verified Source Issues

- `abstract.tex` used `\mathcal{D}=(A,S,U)` before unpacking what `A`, `S`, `U`, and `\Opt` mean in plain English.
- `01_introduction.tex` opened with theorem counting and a theorem list rather than a readable problem statement.
- The original Theorem 1.1 prose hid the discrete typing that makes the Lean theorem valid.
- `02_formal_foundations.tex` already contains readable definitions, but those definitions appeared after the reader had already been asked to decode dense notation.

## Non-Negotiable Rewrites

- The abstract must open with the motivating question.
- The abstract must define `A`, `S`, `U`, and `\Opt` in plain English before compressed notation.
- The introduction must not lead with theorem-count signaling.
- Theorem 1.1 must match the current Lean typing exactly.
- The early theorems must read as one derivation chain, not as isolated claims.

## Rewrite Order

1. Abstract
2. First two paragraphs of the introduction
3. Theorem 1.1 and its immediate consequence text
4. Connective lead-in sentences for the early theorem chain
5. Minor cleanup of Section 2 only if needed to keep the new opening consistent

## Acceptance Criteria

- The first page is readable without prior Lean context.
- No high-salience symbol is introduced before the reader knows what it denotes.
- The early theorem list reads as a connected argument.
- Theorem 1.1 no longer invites the `\varepsilon \geq 1?` objection.
- No prose theorem is stronger than the current Lean theorem.

## Outreach Implication

- Do not re-engage with a request to read the whole framework until the front door is fixed.
- If re-engaging, point to one revised section or one corrected theorem, not the entire paper.
