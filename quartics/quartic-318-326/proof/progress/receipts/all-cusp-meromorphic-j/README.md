# Genuine meromorphic j on the actual compact all-cusp curve

Strict Lean 4.35 replay and exhaustive recursive axiom audit: PASS, 34 declarations in four producer modules. Only propext, Classical.choice and Quot.sound occur.

This packet binds the genuine modular j-function to the actual compact connected complex analytic all-cusp curve, rather than supplying a meromorphic modular-cover model as a hypothesis.

- `AllCuspJ318` defines genuine descended j on the dense original quotient and totalizes it to zero at the attached poles. It identifies the exact function on every actual filled disc and actual complex chart as G(q^w)/q^w, with the already constructed conjugate width w.
- `AllCuspJHolomorphic318` proves holomorphy at every point off the finite cusp complement in the registered all-cusp complex manifold.
- `AllCuspJPole318` proves that the actual chart germ at every cusp is meromorphic with exact pole order -w. Its reciprocal is analytic at zero and has exact zero order w.
- `AllCuspJGlobal318` proves meromorphy in the actual registered chosen complex chart at every point. The negative-order locus is exactly the distinctly embedded finite cusp complement, so the pole set is finite. Holomorphy off the cusps is used to exclude any extra poles.

The assigned finite value zero at a pole is Mathlib's totalized meromorphic-function convention. The honest continuous infinity-valued extension remains `AllCuspInfinity318.jInfinity` from the prior packet.

## Exact boundary

This does not identify the compact analytic curve with the particular algebraic modular cover or construct the arithmetic, PEL, Hodge or Arakelov comparison. It does not register a complex atlas on the OnePoint C target. Exact local pole data do not by themselves prove a global algebraic comparison or numerical degree/genus formula.

The source here is the actual Gamma1(N) quotient and its all-cusp filling for N >= 5. The specified arithmetic point-level X_H requires the corresponding diamond quotient and an actual algebraic-moduli comparison. In particular the auxiliary elliptic modular curve is not silently identified with a PEL/Shimura source.

## Replay and provenance

Run `bash build-all.sh` while holding the common exclusive heavy-compile lock. The four producer modules and exhaustive import-all recursive audit are rebuilt sequentially with `debug.skipKernelTC=false`. The audit includes public, private and generated declarations and rejects every axiom except propext, Classical.choice and Quot.sound.

Imported predecessors use the pinned checked cache; this is not a fresh replay of the entire Mathlib/dependency closure. The receipt binds exact sources, logs and predecessor receipts. This is author-checked continuation, not an independent review. Frozen files are the receipt whitelist plus receipt and SHA256SUMS; compiled artifacts are excluded. No shared repository, manuscript, branch or PR was changed.
