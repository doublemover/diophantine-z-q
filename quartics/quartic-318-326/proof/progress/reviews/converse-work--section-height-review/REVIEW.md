# Independent review: actual all-place section height

Accepted. The two frozen modules were read line by line, copied into this review, and rebuilt with strict kernel checking. The copied recursive audit checks 42 declarations with only propext, Classical.choice and Quot.sound. Copies are byte-identical to the frozen sources.

The actual `NumberField.mulHeight_eq` formula supplies infinite-place multiplicities and the norm-normalized finite absolute values. The local maximum is positive for a nonzero coordinate tuple even if individual coordinates vanish. Its finite multiplicative support is proved by restricting to nonzero coordinates before taking the finite supremum. Consequently every logarithmic finite sum used later has genuine finite support.

`FrameNorms.normalizedDegree` has the correct sign: minus the weighted sum of logarithmic frame norms, divided by [K:Q]. The exact section identity adds the logarithms of local section maxima to this degree. Under finite integrality those terms are nonpositive, so common vertical zeros improve the upper bound rather than create a missing error. At infinity the multiplicities sum to [K:Q], giving exactly log C after normalization. No unproved positivity assumption on C is used: a nonzero local section and the archimedean bound force it positive when logarithmic monotonicity is applied.

Frame independence is checked using the actual scalar product formula, derived from the height of a one-coordinate tuple. Rescaling a frame by c multiplies each local norm by |c|, whose weighted log sum is zero. The result therefore is not a detached scalar bound with an arbitrary degree label.

`rational_ratio_height` uses the actual pair [a0:a1], with a0 nonzero and a1=q*a0. Scale invariance and the proved rational base-change height identify its degree-normalized NumberField height with the ordinary rational height, including q=0. No degree bound on the number field is required. This permits the finite auxiliary extension used to extend a point of the proper Shimura stack without affecting the bounded isogeny field.

For the source application, the sections are J²q0 and J²q1, the ratio is t and the bound is J²*4Cmet. The selected point avoids infinity, so q0 is nonzero. The remaining geometric inputs are exactly the realization of the frame, actual local section norms, and identification of the normalized degree with the evaluated bicanonical/Hodge line. This packet does not assume a final projective-height inequality and does not construct those geometric objects in Lean.

## Reproduction

Run `bash converse-work/section-height-review/replay/run.sh`. This freshly compiles the installed Mathlib Projectivization source in an isolated symlink overlay before compiling both copied project modules and their recursive audit. No Mathlib source, shared cache, repository file or frozen producer file is edited. The overlay and generated object files are reproducible and need not be vendored. The receipt binds source copies, upstream dependencies, scripts and logs.
