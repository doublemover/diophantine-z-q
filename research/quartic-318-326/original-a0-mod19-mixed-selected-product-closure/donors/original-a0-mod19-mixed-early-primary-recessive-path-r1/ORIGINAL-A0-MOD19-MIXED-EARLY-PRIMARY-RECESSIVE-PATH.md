# Product-depth coverage and one earlier recessive path of the selected mixed pair

Fix the same actual compact label tuple, fresh shared original key and literal 19-unit detector scale. Keep the selected plus primary-1 simple pole x=0 and minus alternate-1 simple pole y=0, feeding the same split leaf. This note gives a chart-coverage table for the independent product of their depth-d coordinate blowups, and proves the **primary recessive / alternate finite nonzero** cell at every earlier depth. It does not infer the unresolved cells merely from this table.

## 1. Candidate coverage table on one actual proper product model

Write π=19, d=v₁₉(Z)/2 for the actual common pole weight, and U=π^d w p₁^+, V=π^d w a₁^− as in the exact reciprocal-pole proof, where w is the fixed unit square root of the stripped weight. Let B_x and B_y be the independent coordinate depth-d blowup chains, following each π-chart origin. Their product is proper over the original local pair of arms, and this uses the same x,y pole coordinates throughout. For each arm every point over the selected original centre is in exactly one of the following chart **types** (different charts may overlap within a type):

* **S, recessive.** At an earlier complementary chart j, 0≤j≤d−1, let a=x/π^j, u=π/a. If its next π-chart does not contain the point then u=0, and the normalized x-pole is a unit times a^(d−j−1)u^(d−j). This vanishes there. Same classification for y.
* **A, finite nonzero.** In the last π-chart x=π^dX with X≠0 in the residue, the normalized pole is finite and a unit. The analogous coordinate on the other arm is Y.
* **P, supercritical pole.** In the last π-chart x=π^dX with X=0 in the residue the normalized pole has its exact simple pole 1/X, and analogously for the other arm.

The claim that this lists all chart types is just the blowup cover: at the first step where the downstream π-chart does not contain a point, the complementary chart has u=0; if no such step occurs, the point remains in the last chart. Take this independently for x and y. The following grid then records the candidate remaining work and prior coverage over this one pair:

| primary/alternate | S | A | P |
|---|---|---|---|
| S | Both normalized poles vanish. Existing doubly complementary product-node proof at the last named node only; other corners use the same candidate but are not inferred here. | **Proved below at every j**; simple alternate-only trace directions. | Candidate single dominating (U−V)^32 pole; not proved here. |
| A | Candidate simple primary-only trace directions, with α term and the original critical-value exclusion. Existing named last V-axis point only. | The mixed genus-15 trace torus and its quotient are proved separately; no assertion here about every graph stratum in that torus region. | Candidate single dominating (U−V)^32 pole; not proved here. |
| P | Candidate single dominating (U−V)^32 pole; not proved here. | Candidate single dominating (U−V)^32 pole; not proved here. | The raw X=Y=0 pole corner is covered by the separate four-stratum proper graph proof. |

This is a table of the product-cover restrictions, not a statement that every earlier-scale exceptional component has already been handled. We now address a cell where a trace can actually cancel and could in principle create a new contact-balanced residual cover.

## 2. The same alternate trace appears at each earlier primary depth

Fix j in the S-primary row. In its complementary plus chart and the alternate's last π-chart,

    a=x/π^j,      u=π/a,       Y=y/π^d,
    π=a u,        x=π^j a,      y=π^dY,       Y a unit.

This chart is étale over the regular node model with coordinates a,u,Y as in the named last U-axis proof. There is only one complementary node factor because the other arm is in its last π-chart. The actual normalized split-pole inputs are regular here, with U a unit times a^(d−j−1)u^(d−j), and V=B/Y on the residue of interest, B≠0 a constant determined by the genuine alternate pole and stripped weight. Their exact integrality follows by stripping those two literal simple pole terms, not by identifying them with their reductions. The shared stage-12 addition (U−V)^2, and the weighted late J root π^d w(5P₀²−1)−2P₀²U, are both regular. All other coefficients near the selected centres are integral and have their checked positive additive weight depths.

On u=0 one has U=0 and the actual stripped reductions are

    bar(f_+)=(1+(B/Y)²)^16,       bar(f_−)=1.

In the geometric fibre over the fixed original point the remaining coordinates on this open are a,Y if j≥1, and just Y with a=0 if j=0. This is exact: the coordinate blowup product is pulled back by the actual étale coordinates and then restricted to that fixed fibre, so its function field has no extra variable-degree extension. The alternate value B/Y is independent of a: y=0 on this geometric fibre and the stripped pole numerator is evaluated at its fixed original selected centre. The primary alpha term vanishes as U=0.

Away from the trace roots the denominator f_++f_- is a unit. The contact is regular in π^e O, so δ=1 in reduction and the normalized étale cover has rational split sheets on this geometric open. The actual target map extends over the regular cover and is constant on them. At a trace root there is one of the 32 simple nonzero values V_*=B/Y_* with

    (1+V_*²)^16+1=0,           derivative 32V_*(1+V_*²)^15≠0 .

This follows from values 2 and 1 at the two possible derivative-zero loci. No choice of a or new residue arithmetic enters the root set.

## 3. Exact local cover at all such earlier trace directions

Here f_+ and f_- are units and their sum has nonzero derivative in Y at every point on the named direction. With e=v₁₉(κ)>0, set

    ℓ=(f_++f_-)/((κ/π^e)f_+f_-),      c_fold=(a u)^e/ℓ.

This ℓ is an actual replacement étale coordinate. After stripping the denominator in δ=1−β(a u)^(2e)/ℓ² and using the sum and difference coordinates, the exact normalization is the binomial

    M N = a^(2e)u^(2e),        π=a u,

up to the fixed unit β in one coordinate. It is S2 and regular off the codimension-two possibility M=N=0, as in the earlier exact axis model. Above any fixed geometric direction point with a=0, proper peeling in the two parameters a,u gives only rational geometric curves. With a≠0 the same statement follows by the one-uniformizer version with u; there is no additional ramification from the unit a.

There is also no hidden nonrational residual curve **dominating** a trace direction line: when j≥1 its function field is the rational k(a) after naming the finite constants, and at its generic point a is a unit. Replacing ℓ by ℓ/a^e yields the exact unit-depth equation c_fold=u^e/(ℓ/a^e). The balanced contact conic is rational over k(a) and the split chain needs at most a finite extension of constants, not of the variable field. Its target image therefore factors through the rational a-line and is constant. For j=0 the direction is just a point, already treated.

By BLR extension on these regular models and the proper main graph comparison, there is no nonconstant elliptic image over any of the named S-primary × A-alternate charts, including their earlier-scale generic direction lines and all closed centres of those lines. This adds a genuine earlier-path exclusion, not just the formerly selected last U-axis direction. The other product cells in the table remain limited to their separately stated scope.

Exact bindings: actual mixed shared-pole strip and selected preimages list b6cac3561eaf495332b35cd62ba95b0b6deadfd038a3ede16951f61d4a980d0f; named last mixed U-axis list a824f7a8130edd208fa6eef9f3c5c7949217651c6aa830c3db0dcf334124a55f; mixed V-axis list b73c132732d824bd907189b1324274e63b50aee0bf5f9e9b0d1dcca87249a1c8; both-small last product node list f81803ee8feaaa5950bf5eed7cc9f5199f20ad6767f4cfb6a4446eee5cd3afb0; raw pole corner closure list 01d7b092c923b62d883a50059b529e97af3e48117852b6cc491212a617a7a997; exact conic chain list ccdac523d869a73eaa4f17658e53a19983382fc53608de4ffb79d075cb8b920f; [BLR, Néron Models §8.4 Cor. 6](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf). No prime scan, numerical key or global conclusion.
