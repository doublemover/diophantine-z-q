# Independent review: two incompatible reductions on the actual genus-nine curve

**Exact mathematical and replay PASS, 2026-11-21.** I verified every
own and upstream binding of author manifest
41da366d16fe3b689b0d6c089d1362bc4e2d2e2599e16178d899fe4ef4031ce9,
paper 944702f98e87ef4ff25464bd77a55c91c550394c38cfe96dc0e3d5454518ab4d,
and byte-exact replay. This conclusion combines only with the previously
reviewed everywhere-local genus-nine curve (manifest 8cac182a…),
not either separate candidate on the original Kummer.

The quotient equation is obtained from the *ratio* of the two
actual square conditions and the exact fractional-linear change
x=20/(q+1)−15. It is E*: y²=x(x²−2x+65), with P=(5,20),
T=(0,0). On the first 2-isogeny side positivity and valuations restrict
the image to 1,5,13,65, all realized by P and T. The other side has
a′=4,b′=−256; it realizes both unit signs, and the possible class 2
fails modulo 8 after division by 1,16,64 according to the depth of the
primitive U. Class −2 then fails by multiplication by the realized −1.
More explicitly, the index of 2E*(Q) is the two image sizes multiplied
and divided by 2: the kernel of the dual isogeny meets the image of
the first trivially because E*[2](Q) is precisely its first kernel.
So the index is four and the rank one. Good-place torsion counts
6 and 10 at 3 and 11 give exactly the order-two rational torsion.
P has odd index in the free quotient, since its x-class 5 is neither
of the torsion classes 1,65. No assumed generator or saturation result
is needed.

At 17 the original prepared W is 1 mod 17, the normalization
denominator is a unit, and v₁₇(β)=1, making δ a square unit.
Both F and G must have odd valuation at a putative rational point.
Only q=1/4 or −3/4 in reduction can do this, and only 1/4 is
square. Thus R reduces to ±2P. At 131 the unchanged source
δ is 82·131 mod 131², β is square and −3 is nonsquare.
Negative q-valuation would make βG have nonsquare unit class
−3; hence q has positive valuation and R reduces to ±P.
For the same global point take mR=nP+eT with m odd.
At 17 P has order eight with 4P≠T, forcing e=0 and even n.
At 131 P has order fourteen, forcing odd n. I independently
recomputed both complete finite cycles and the dyadic exclusions.
The contradiction applies to all rational points because the
real and boundary analysis of the preceding exact paper already
puts every rational point in the useful open.

This is an everywhere-local, globally insoluble **specific
genus-nine multisection on the literal scalar**. It is not an
obstruction to the full Kummer, the alternative genus-one route,
or the fixed-lambda fibre. No Lean compilation or remote write.

Reviewed by the independent proof/CI lane.
