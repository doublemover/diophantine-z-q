# Independent check: fixed materialized h/J, auxiliary height at most 100000

Input authors' exact note 7587386bf4d7c12278fd1f18ea50d94db5e729a9fcef240987f909f201e3978c,
script e2bc75f4a89457f3a5f1c849ced9cdc2d00dba5f6cd2710bbeb801d308ce2d55,
JSON c1fa522401da1d6758a5e131dc8ca07619363bed094e0855a2c26c6d76cf8ab8.
The original command replay produced byte-identical JSON. Adjacent independent checker
uses only Python standard library and accepts a path containing
EXACT-SCALAR-SPECIALIZATION.json and FIXED-H-HEIGHT-SIEVE.json.

I independently recomputed actual h and J by the same local-depth condition;
all 41 recorded distinct primes are prime. For the 36 nonsupport primes, I
rechecked every split/inert order by full annihilation and all prime-divisor
tests, scaled the actual generator on the same smooth reduced cubic,
evaluated both literal chart indices h and s−1 with unit denominators
(allowing regular zero at O), then recomputed H, I, W, b, and delta.
The five support rows use the already verified original formal-depth
congruence W=1 there: no replacement of the global scalar. The CRT prefix
orders were independently checked in the materialized-scalar cold receipt.

The homogeneous test is necessary even when p divides the denominator d:
d²H is p-integral because its square is p-integral, and reduction can be
any square INCLUDING zero. At d≡0 the test is 9βa⁴, not a division by d;
in particular (a,d)≡(0,0) is allowed. Independent periodic mask generation
by recursive concatenation reproduces every original count; the clipping
keeps exactly 1≤a≤100000 including both endpoints. The exact search covers
10^10 positive numerator/denominator pairs before any gcd restriction.
By evenness it excludes negative numerators as well. There are 22, 3, 1,
1, 0 unsigned pairs after rows 27 through 31. The last survivor is the
reduced pair (70803,71176), removed at p=379. The constraints are at
distinct primes; no statistical independence of the bounded pairs used.

The fixed scalar has δ≠0 and nonsquare β, excluding k=0 (and the
quartic's projective k=∞ has nonsquare leading coefficient 9β).
In the preceding t-chart F9(t)=0 has no finite rational t, so ordinary
rational t supplies a finite k. Also the projective t=∞ in that chart
would require 1−9D a square; at p=13 it is the unit 7, a nonsquare.
These are checks of the existing auxiliary cut only: no restriction on
other constructions or other h/J, no global torsor insolubility,
no bound on the possible height of a rational point, and no rank/Sha
or underlying PointPair obstruction proved. No Lean/build involved.
