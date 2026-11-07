# Independent actual height coverage review

PASS:13 source modules copied to this directory and rebuilt with debug.skipKernelTC=false; recursive audit110 declarations, standard axioms only. The producer counted59 public results; the recursive count also includes definitions and generated declarations.

Mathematical scope checked: rational heights use primitive numerator/denominator Bezout at each actual finite place; primitive nonrational quadratics have positive leading coefficient and exact gcd1; actual roots in Q(sqrt2) force the integer discriminant2k²; normalized finite Gauss products and conjugation invariance yield finite height equal to the leading coefficient; the two actual real embeddings supply the Mahler factors; simple-subfield transport proves absolute height equals half the relative logarithmic height for every field element. The polynomial coefficient box therefore applies to the original actual absLogHeight definition, without a detached height model or residual Mahler assumption. The base point polynomial and both-root>1 bounds give exact xHeight(P)=log41.

No issue found in the final PolynomialHeightCoverage, all-element normalization, or base height interfaces. This review does not assert canonical height, rank, or contact-height49/8. Sources and exact rebuilt artifacts are retained here; hashes are in REVIEWED_SHA256SUMS and output in rebuild.log.
