# Current source-specific completeness audit

## What this lane now establishes

The literal 318-variable source is covered by an explicit conditional
integer-to-witness assembly, including all 288 defining rows. The assembly
retains PP and RC as named global theorems, whose actual manuscript proofs
have been examined rather than treated as absent axioms. The source-specific
proof notes and local Lean statements below strengthen and audit the producers;
they are not a kernel-checked global arithmetic theorem.

### Literal witness and prime choices

- `COMPLETENESS-ASSEMBLY.md`: current source rows, witness order, domains,
  coherent signs, zero branches, compressed bridge, pole normalization.
- `PRIME-PATTERN-AUDIT.md`: actual simultaneous Gaussian-prime proof, geometric
  and analytic hypotheses, source specialization, order separation. No concrete
  defect found. Primary-source retrieval limitations are recorded there.
- `BRANCH-CERTIFICATE.md`: the required fourth-power ray special case derived
  from quadratic reciprocity, explicit halving and opposite-branch sign.
- `ANCHOR-COMPLETENESS.md`: every local place, Hasse–Minkowski and affine
  denominator. Independent integer descent/anisotropy additionally formalized
  in `../prime-witness-bridge/AnchorAnisotropy.lean`.

### Actual odd arithmetic producer

- `detector-producer/DETECTOR-PRODUCER.md`: actual nonzero point, open-image
  Kummer detector, compatible finite stages, auxiliary intersections and
  finite-field evaluation. Fresh BFH, Serre, DD and CST scope checked.
- `cm-producer/CM-PRODUCER.md`: actual weighted CM torsor reduction, one CJ
  sign fiber, normalizer-generated signs, level-two orientation, integral stack
  mass before reduction. Independent source cross-review is
  `../cm-cross-review/CM-CROSS-REVIEW.md`.
- `theta-producer/THETA-PRODUCER.md`: actual local weights, common rank-three
  cover, dyadic quotient, global rational splitting, all-cusp holomorphy,
  coefficient extraction and arbitrary-phase all-index neighbor recurrence.
  Fresh original Weil checks included. Independent normalization review is
  `../soundness-local/theta-peer-review/REVIEW.md`; it does not separately
  validate the all-index neighbor enumeration.
- `odd-coefficient-bridge/STAGE-BRIDGE.md`: phase reduction, actual integer-two
  division in a ramified coefficient ring, finite-stage binary reading,
  same-stage whole-prime omission, all-index precision budget, and fixed
  ultrafilter minimum/stabilization. It consumes actual arithmetic coefficient
  rules, not merely a generic formal trace variable.

### Actual even arithmetic producer and companion

- `even-producer/EVEN-PRODUCER.md`: nonzero reference, scalar local projection,
  dyadic two-neighborhood noncancellation, full-space Waldspurger square
  identity, algebraic field-extension argument, Galois/local-root rational
  phase, good recurrence, square shells and fixed attained minimum. Fresh
  Waldspurger 1981/1983 and Ramsey originals checked. Independent review of
  the local projection/Galois seam is complete: see
  `../even-producer-cross-review/REVIEW.md` and the separate converse
  assembly receipt (§25). No normalization or rationality mismatch was found
  within that explicitly bounded review scope.
- `rough-companion/ROUGH-COMPANION.md`: fresh Hoffstein–Luo scope, actual
  five-new-prime correction, root sign and local squares for the varying
  auxiliary curve, dummy/exclusion order, partitionability, fixed-source
  valuation constants and noncircular dependency order. The scalar/address/
  Boolean producer is consumed at the separate converse audit's declared scope.

## Joint work that is not silently attributed to this lane

The current `../converse-work/restricted_converse_boundary.md` records the
separate worker's fresh source checks. In particular its §22 establishes the
actual common alphabet, stationary/two-symbol address networks and single
finite-stage choice before prime realization; §23 establishes the actual
modular trace/inertia coefficient rule, including a directly checked published
unary-transformation input. The same worker freshly checked the native
index/height calibration and reported original Kato rank-zero scope. These
are cited as that worker's proofs, not automatically inferred from a PASS
marker or from earlier historical review.

The earlier note that forward rank-zero was not independently inspected *by
this lane* remains accurate. It is no longer a joint uninspected-source boundary:
the converse worker's original Kato 2004 p.235/Corollary14.3 check explicitly
includes the coefficient prime two and has no residual irreducibility hypothesis.

The full joint RC conclusion must be made by assembling all retained producers
and their exact dependencies. This progress index does not declare that global
conclusion before the separate worker's final remaining-boundary report.

## Reproducible formal scope

`bash verify_all.sh` runs 15 explicitly listed modules, including the independent
anchor module, plus exact finite source accounting of all 288 rows. There are
92 named theorem/lemma declarations in those modules. Their proofs cover local,
finite and algebraic substeps. They do not formalize analytic prime existence,
Waldspurger, Weil theory, Hasse–Minkowski, Kato, or the whole restricted converse.

Each producer subdirectory has a receipt binding its text, formal source and
retained primary sources by SHA256. The original manifest is supplemented by
`audit-manifest.json`; the latter distinguishes rerun status from mathematical
scope. No PR or manuscript edit was made by this lane.
