# Original detector slot 190: an exact fixed-index support obstruction

This paper appendix concerns the **original unscaled detector** at slot 190
of the 318/326 source for $a=0$. It keeps the retuned $h,J$ identified
by the checked scalar packet, the explicitly admissible Lucas labels,
the original contact polynomial, and the original 16-leaf detector fold.
It contains no Lean intake, no proof of analytic prime-pattern existence
and no completed table or rational point.

## Main conclusion and its limits

Read [the final finite-support theorem](linked-detector-known16-exhaustion-r1/ACTUAL-SLOT190-KNOWN16-EXHAUSTED.md).
With this $h$ fixed, write the contact parameter as $t=(R/D)^2>2$
with positive coprime $R,D$, $v_2(D) \ge 2$ and $3 \cdot 17 \mid D$.
If a literal PointPair exists at slot 190, at least one of
$2R^2+D^2$, $R^2+D^2$, $2399R^2-D^2$, $407R^2+32D^2$
has an odd exponent at an odd prime **outside** the stated sixteen-prime
list. Such a prime must lie in the actual fixed coefficient-exceptional
set and cannot divide $D$. No such actual odd contribution on a
viable contact parameter or rational PointPair is supplied here. The sixteen nominated primes are a **finite
tested part** of the possible support, not a computation of the full
exceptional set. The theorem does not rule out other square parameters,
does not apply this finite exclusion to nonsquare $t$, and does not
rule out the original ordering that chooses $h$ after seeing contact
support.

The separate [fixed-index genus-five result](linked-detector-fixed-index-genus-five-r1/ACTUAL-FIXED-INDEX-GENUS-FIVE-DIRECT-SEARCH.md)
allows arbitrary rational $t$ and proves finiteness on a finite family
of covers using Faltings. It is not effective on the uncomputed full
support and does not enumerate or rule out their rational points.

## Exact source and dependency order

1. [Fixed retuned scalar](rc-linked-four-pole-common-q-r1/ONE-Q-FOR-FOUR-POLES-FINITE-INCIDENCE-AND-LIMIT.md)
   and its [exact input](rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json).
   The appended recipe for old-to-new scalar retuning is replayed; no
   four-pole prime-pattern or selected-point existence claim is consumed.
2. [Same fixed scalar, original detector prefix](linked-detector-fixed-scalar-prefix-r1/ACTUAL-FIXED-SCALAR-SHARED-DETECTOR-PREFIX.md):
   explicit Lucas labels, genuine guards, original pre-pole rows,
   positive ranges and simultaneous small local data. These are not
   all-place denominator guarantees.
3. [Literal PointPair valuation and exceptional set](linked-detector-fixed-index-necessary-r1/ACTUAL-DETECTOR-POINTPAIR-DENOMINATOR-GUARD.md),
   followed by the [genus-five and quotient calculation](linked-detector-fixed-index-genus-five-r1/ACTUAL-FIXED-INDEX-GENUS-FIVE-DIRECT-SEARCH.md).
4. [Saturation, exact E₂ rank-zero test and fifteen-prime variant](linked-detector-finite-saturation-r1/ACTUAL-190-FINITE-CONTACT-ESCAPE-CERTIFICATE.md),
   then the [exact extension allowing 5](linked-detector-finite-saturation-plus5-r1/ACTUAL-190-ESCAPE-5-ALSO-FAILS.md).
5. [All sixteen status combinations](linked-detector-known16-exhaustion-r1/ACTUAL-SLOT190-KNOWN16-EXHAUSTED.md).
   The [independent review](joined-slot190-known16-cold-r1/INDEPENDENT-KNOWN16-REVIEW.md)
   computes the forced root residues directly, rather than calling the
   author's determinant and bit-mask procedure.

The source notes pin the corresponding literal module declarations
in the `forward-actual-two-descent-root-divisor-orders-r5` experiment.
The package contains the exact older scalar input files needed by the
included retuned-prefix checker. Historical source and replay files
retain their bytes. The paper uses the classical Faltings finiteness
theorem and elementary fixed-curve two-isogeny descent; neither is
asserted to be formalized here.

## Reproduction

Use Python 3.10+ and the ordinary `sha256sum`, `cmp` utilities.
No network, external Python package, or Lean executable is required.

    sh replay.sh

This compares exact author and independent outputs after checking the
top-level and per-step SHA-256 manifests. The coefficient-fold
finite-field controls exercise the leading-term argument; they do not
materialize the enormous literal detector coefficients. No future
extra-prime discovery or unreviewed extension is included.
