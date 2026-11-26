# Coterminal institutional 3/2-L-adic H24

- `paper.pdf` and `paper.tex`: full written mathematical argument, five marked theorem ports and typed graph.
- `check.py`: exact finite integer tests of the circuit, signed path expansion, modular readback, Gray seam, original prefix monoid, first-hit valuation and majority identities.
- `original_prefix.py`: extracted unchanged prefix class and fold from `Braided_Gauge_H24/wire.py`.
- `original_codec.py`: unchanged original four-Golay and Collatz quotation functions from `Institutional_LAdic_BQP`.
- `canonical_codes.json`: full written theorem quotations in all four Golay encodings, with their Collatz-Gödel addresses and ordered parent references.
- `receipt.json`: actual check counts and scope.
- `Coterminal.het`, `.lean`, `.agda`: elementary formal consequence ports; not full formalizations of the paper or quantum universality. No corresponding proof kernels installed, so no replay claimed.

Replay: `python check.py` (standard library only). Compile `pdflatex paper.tex` twice. The finite exact tests materialize small state vectors and paths only to independently check the symbolic equations; they are not a polynomial simulation of general quantum computation. The BQP-completeness theorem uses the standard universal gate theorem. The Skelet 17 nonhalting macro theorem is imported from Xu and its Coq formalization, not re-proved. The actual seed-8 Antihydra observation has only a finite scope. The shared depth-64 prefix is a different, explicitly defined ternary grammar. No full older H24 executable has been rerun in this continuation.
