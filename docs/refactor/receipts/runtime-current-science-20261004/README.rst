Current source science acceptance
=================================

The completed ordinary outputs from source
``9e838be5646a0dd414630f8b84951238387df2e7`` pass six comparisons
against both retained, qualified v12 native outputs for the original 3D
monolayer, Speckles and Beginner pipelines. The existing full measurement,
directed relationship, physical inventory and image policies are unchanged.
Both original 3D volumes require exact pixels. Ordered source-reference
counts remain 180/2/10; current input and retained native output hashes match.
The result file retains each comparison and every compared output hash.

This validates the integrated physical-column, source-metadata, output-kind
ownership and RelateObjects reader changes on current dependencies.

The v13 timing campaign remains rejected: Speckles produced a successful
authoritative W001 outcome and its three CSVs, but its asynchronous progress
stream lost the completion tail. All jobs are terminal and guards pass. No
second ordinary sweep or fresh native worker ran. These six comparisons are
science-only acceptance against retained native data, not a fresh paired
performance result or the retired original #496 bounded graph proof.
