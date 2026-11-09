# Forward compressed-anchor witness construction

Status: first strict Lean compilation and distinct non-author review pending.
This isolated experiment is not in the accepted progress manifest. It does not
prove integer-to-source completeness or any global prime-pattern/converse input.

## Historical and current scope

The actual earlier argument is `proof/progress/receipts/completeness-work/COMPLETENESS-ASSEMBLY.md`,
Section 4, and `docs/arithmetic.md`, “Completeness of the compression.” They
construct the parameter `(k*f*y-m)/(k²+D*f)` for a chosen square-abscissa point.
That argument is prior justification, not a newly discovered mathematical gap.
The accepted `CompressedPoint318` and `CompressedTranslation318` modules
reconstruct points from already supplied source rows; they do not construct
this block's coordinates in the forward direction. This experiment supplies
that forward algebra and binds it to the seven literal raw residuals.

## Application contract (nine obligations)

1. **Source input.** The carrier is the existing `ConcreteG8Domain.K`, with the
   existing constants `CompressedOrientation318.k`, `m`, and `D`. The input is
   any pair u,v in that field with u nonzero and v²=1−Du⁴. The known constant
   identity m²=k⁴−D is consumed from `CompressedPoint318.constant_equation`.
2. **Constructed objects.** Set f=u² and s=(kv/u−m)/(k²+Du²). Set the stored
   rational norm root to u.re²−2u.im². The nine coordinates written are exactly
   33,34,35,36,37,74,75,76,77. The latter four store f*s and f*s².
3. **Quantifier/index coverage.** The construction accepts every such actual
   chart and every base assignment. It proves all r32 through r38, including
   the four multiplication-gate rows, both compression components and the
   norm-square row. v=0 and s=0 remain allowed. No other row is claimed.
4. **Domains.** u≠0 is explicit. The other denominator is proved nonzero via
   the original positive real embedding: k² has strictly positive image and
   Du² has nonnegative image since D=(3−sqrt(2))². No division is justified by
   an unproved solution predicate or retrospective point choice.
5. **Maps and orientation.** The compressed A equals kv/u. Therefore its x
   and y reconstruction is exactly 1/u² and v/u³, including the original sign
   of the ordinate. The statement is not merely equality of abscissas or
   existence of another point on the curve.
6. **Literal consumer identity.** `literal_rows` targets the unchanged
   `Raw318FinalReplayData.r32` through `.r38`; coefficients and indices are
   imported from the accepted raw data, not copied into an alternative source.
   `reconstruct_original` targets the existing `CompressedPoint318.xH/yH`.
7. **Framing.** `fill_other` preserves every coordinate outside the listed
   nine, and `fill_input` preserves coordinate zero. Changes to those nine can
   affect other source rows: this is not a claim that arbitrary existing
   solutions stay solutions or that the complete source has been assembled.
8. **Evidence/acceptance.** Intake hashes bind the exact new source. Hosted
   first compilation with kernel checking and private-inclusive recursive axiom
   audit is pending. No independently accepted conclusion is asserted.
9. **Downstream boundary.** Actual simultaneous point/chart selection,
   coherence across the other seven charts, guard inverses, detector and pole
   witnesses, semilocal anchor witnesses, and all-288-row assembly remain open.
   This packet neither changes nor accepts the PP/RC theorem applications.
