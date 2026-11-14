# Independent fourth Picard source and propagation review, run 43519890754

Reviewer: lean_review_resume. No Lean/Lake invocation, source edit or push.

## Bindings
- Packet: original-five-kernel-norm-equivalence-r9, predecessor r8 at head 58753ec5f3b41268c5ceedae5264593b4f2aa0de.
- OriginalTwoOpenReducedCocycle318.lean before `5c1d03ef4d0e2be5ca91188079cff51241b046dc7b47dffeada31cb7610b0637`, after `028ca790008a22b1d1ef695d97de039e94907894ddaffba4def3dc2a84be4704`.
- intake.json `7b81115758238e7885240d66e66a49e13467ba916da41e038467906dcd40e966`.
- README.md `aba8b98f23f0fc6705e00da5873cb3c43deda1a1ec97cde8f99d5683a87cae1f`.
- Reviewed APPLICATION.json snapshot `0685833585db8a4d484b75b6a5988f35b9d227584cf8a80f6654874790753da0`. Later report-reference metadata may change its hash, not these source/intake/contract bindings.
- Exact failure log `1b427f340544b9d2fd0fb7d8dd5a1f1697492dfd3f94b2408125839cdcb1c99b`.
- Native primary LinePullbackFrames318.lean `53cc2280e443720c582c7a10f6cda23c5613ef205ea37c1ffb218d21047f441f`.

## Source findings
No source-level blocker found. All three edits respond to the exact hosted diagnostics, not hypothetical later errors.

1. frameAlongOpenEq abstracts the entire dependent frame type over an equality of Scheme opens; subst eliminates that equality before returning the original frame. Its Scheme universe matches this existing universe-zero API, and it introduces no assumption about the original scheme. The application uses precisely fullOpen_eq for the same original Bool-indexed affine open. OriginalThickenedFrameCocycle318.opens is exposed as fullOpen, and AffineHOnePointedDeformation318.thickOpens is exposed as the same first-projection preimage. Thus the equality endpoints match the observed dependent type mismatch. No frame, module, open or restriction map is replaced.

2. reduction_preimage states reduction-preimage of first-projection-preimage equals the original open. Applying congrArg of first-projection preimage, then symmetry, gives exactly thickOpens equal to first-projection-preimage of reduction-preimage of thickOpens. le_of_eq supplies the required stability inequality. This deliberately avoids the old rewrite that matched the outer projection-followed-by-reduction composite instead of the valid inner reduction-followed-by-projection law. Direction and all full-open domains were checked against both source definitions.

3. The native preimage_cover theorem requires only a morphism and a complete open cover. TwoOpenAdditiveCocycle318.cover uses the original hc : U supremum V equals top and covers both Bool indices. Their direct composition supplies exactly the unchanged reconstruction cover type. The IsIntegral X instance required by the old thick_cover wrapper is absent from these actual native prerequisites and is not added to the original target. SplitPointedCocycleNormalization318.reconstruction remains the same actual pointed line, reduction, projection, normalized frames, gauge and module-sheaf reconstruction.

The public declarations and hypotheses remain unchanged. The only new declaration is private frame transport, with all its hypotheses explicitly used. cocycle, overlapUnit and overlapUnit_reduces source bodies are unchanged. Existing resource/transparency options are unchanged. No axiom, sorry, coverage restriction or surrogate cohomology label was introduced. I read the immediate OriginalHOnePointedSurjection318 consumer; it continues to use this same overlap unit and reconstruction. Its later representative_class still invokes an integrality-sensitive old wrapper; that unchanged, unreached issue is not fixed or claimed passed here.

## Propagation and provenance
The exact root source set has 213 files; 212 are byte-identical to r8 and only the source bound above changes. Ordered intake closure is identical. All APPLICATION sources and evidence bindings recompute correctly. The retained exact hosted RESULT.packet_sha256 equals r8's actual intake hash `27e02f3c031a73e8ccc57b18ec93d665069735f016710bfccc63d9faeb3aada3`. I checked the README's full-object/coefficient/map/hypothesis/consumer contract against the source. The primary LinePullbackFrames source is evidence, not a changed root dependency.

## Acceptance boundary
This is source and provenance review only. The current candidate has not been compiled by this reviewer and is not Lean-passed or independently mathematically accepted. Hosted strict compilation, bounded behavior, recursive axiom auditing and later consumers remain to be checked. Earlier successes do not imply this or the whole packet passes.
