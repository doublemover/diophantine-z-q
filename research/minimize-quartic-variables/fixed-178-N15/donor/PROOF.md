# A literal, practical 180-variable quartic at N=15

**Statement.** Let f be the signed integer polynomial in quartic180-N15.txt, SHA-256
51d39c44672fa8a1a15940357a525babfa169794f460da30b5f186cd3e584d4a.
Under the same arithmetic premises as the reviewed effective 180 and fixed 181,
for each rational X the following are equivalent: X is an integer; there exist
179 further rational coordinates with f(X,…)=0. N=15 is fixed before X. The
literal has 82,777 ASCII bytes, 3,253 distinct monomials of total degree ≤4,
maximum absolute coefficient 365 bits, and coefficient 1 at X⁴. Its 152
primitive integral quadratic residuals square and sum to f. This is a different
polynomial from both the previously frozen 180 specializations and fixed181.

**The actual chart.** Recover the point and comparison geometry from the 180
coefficient family e507e183 at its existing true weights, with one changed
register. Write C=149¹⁵, s=X², z=s+48, and q=u₀+u₁+u₂−3 with its independent
inverse. The existing entries for z and z², the input, 3 arguments and their
complete harmonic caps, both components of the actual four-point sum, and the
signed bilateral role-one marks all stay put. The old scalar W² helper (donor
identifier 104) occurs in exactly TWO rows. In place of those rows insert the
single genuine cubic-pole row x111²=x105·x113 and the scalar interpolation
inverse row (z−48−a₀)v=1, using its released slot for v with zero q,z
weight. The returned scalar retains R=C x113/q, x112=C x113²/q. In the scalar
parity row replace +C x109 x112 by +q x109 and retain every other summand.
These two changes are exactly the previously verified cubic-pole transfer; the
actual rational scalar pole input becomes

    b_s=R³W_s²,    W_s=Z₀⁴/R¹⁰+Z₁²/R⁷+F²/R⁴,

where Z=2·ζ(Q₂)/ζ(H) uses the original elliptic parameter ζ=−x/y and F
is the norm of the actual reference reciprocal. The conic/pole suffix for
b_s is unchanged. No square root of R in Q is imposed or silently extracted.

For β=1−51s, P(B)=B(B−2401)(32B+343), take b₀=705024, a₀=(1−b₀)/51,
A=P(b₀) and L=557·149². Expand the *polynomial* identity
A−P(1−51s)=(s−a₀)²(b s+c)+(s−a₀)d. The final changed row is

    (b(z−48)+c+d v)(1−149R/(L C²))=A v².

This is quadratic: z and v are individual scalar entries and R is the *one*
stored 113 coordinate times a constant after undoing its exact q-weight.
It is not the cubic product Rz² nor a Laurent denominator treated as a new
input. The other replacement rows are quadratic in ordinary integral table
coordinates as well. Since z−48−a₀=X²+705023/51>0 over Q, the unique v
does not restrict the input. If P(β)=A, the identity forces A v²=0,
impossible. Thus R=(L/149)C²P(β)/(P(β)−A) uniquely. The compiler pulls
back all 150 physical rows into the fixed quadratic slots with explicit
word-length ≤2 per monomial before elimination of q; substitution of its
affine expression keeps that degree. The q guard and z² row are retained,
including q≠0. Only four of 152 ordinary rows change after specialization
up to nonzero row scalings and renumbering; the 148 common rows include both
guards, the γ-safe centered marks, all three independent comparison pole
widgets, signed role-one data and actual two-component aggregate. The coordinate
map fixes X in both directions. Rational vanishing of f is equivalent to
vanishing of all 152 rows, since each squared residual is nonnegative in Q.

**Reverse, scalar first.** Do not confuse the one-variable height argument β
with the actual signed elliptic label z. Until that label is recovered use only
the scalar graph. X=0 is already integral; for all other rational X the mod-149
test for X integral at 149 checks P and P−A never vanish. When v₁₄₉X<0,
v₁₄₉(P)=v₁₄₉(P−A)=6v₁₄₉X by the leading cubic in β. Thus for *both*
cases R≠0 and v₁₄₉R=31. At every good scalar prime of positive odd depth m
the three finite W_s term valuations are respectively 2 mod 4, odd, 0 mod 4,
using the even norm valuation; omit a zero component. The raw reference rows
already exclude F=0. Therefore W_s≠0 and 3m+2v(W_s) is odd, so cannot be
negative by the actual pole obstruction. It follows that v(Z₀)>17m/8,
v(Z₁)>11m/4 and v(F)>5m/4. First use m=31 at 149 to rule out the forbidden
torsion and shifted reference values before dividing by the index; their
finite nonzero norm reciprocals are 149-units. The actual finite chart plus
the original formal logarithm at a good reference slot gives a nonzero integer
index a, with vₚ(a)>17m/8, including the allowable two-torsion translation of
the scalar point. This recovers at least p³ for each m≥1 and 149⁶⁶ at m=31.

Use precisely H4.1 at its original five-contact radical M_S(β), including CM,
S={2,3,5,7,11,13,17,37,41,2399}. X≠0 rules out β=1; the 149 test rules
out its three other finite exceptions. 149 is absent from the radical; outside
S the infinite contact and β=1 contact have even order. Outside the scalar-only
loss D=43·67·191·557·702623=215354614883981, using A's exact factorization,
the remaining positive odd scalar contacts have m=vₚ(R)=vₚ(P)>0. Hence with
c_a=abs(a), 149⁶⁶(M_S/gcd(M_S,D))³ divides c_a. By original v62 H4.1 and
its checked elementary consequence, τ=h(β)<2²³⁸M_S³, so
τ/c_a<2²³⁸D³/149⁶⁶<1/4. The latter follows by the strict integer test
2²⁴⁰D³<149⁶⁶. As z=(2449−β)/51, the numerator and denominator immediately
give h(z)≤τ+ln2450<c_a/2. This last affine-height transfer is necessary
because β is not the label tested by the comparisons.

Now use the unchanged true 180 comparison rows with
Γ=S∪{79,89,647,3593}, not S enlarged by D. At each positive odd mark
outside Γ the harmonic denominator is a unit, the cap/pole enforces qR_j≡1
and supplies a successful embedding of the eight valuation-separated mixed
factors. The two signed role-one marks give absolute depth ≥2; one of h,h−1
is a unit and its formal ratio first gives p-integrality of z, without assuming
vₚ(z)=0. Thus n≡z mod p². The other three comparisons and homogeneous Lucas
give Δ≡0 mod p³. At H_j=0 or a zero numerator, the 180 donor's parity and
trace argument still applies; no extra division or nonzero condition has been
added. Both components of the four actual abscissas reconstruct the unchanged
bound B²<40Σh(t_j)+2425 from the effective full-field height input. With
c_a≥149⁶⁶ the original strict v62 numerical inequality excludes Δ≠0.
When Δ=0, z≠n would give log B<240+c_a from the three measured radicals,
J=abs(num(z−n))≤4B exp(h(z)), and h(z)<c_a/2; Lucas gives log B>320c_a
instead. So z=n∈½Z. Writing X=u/d reduced implies d²|2; hence d=1.
The two-contact weighted trace height is not being assumed.

**Forward.** For each integer X, z=X²+48 is an integer ≥48; at X=0 take
z=48, β=1 and the same fresh witnesses (no H4.1 input at β=1). The scalar
preparation depends on X only through its actual R above. P(β)≤−900000 and
R≥(L/149)C²·900000/(A+900000)>2²⁰. The integer valuations at p=2,3,17
give v₂P∈{1,2,4,5}, v₃P=2, v₁₇P=0, whereas v₂A=9, v₃A=4, v₁₇A=1.
Thus 1−A/P and L/149=557·149 are squares at each of these places. For this
fixed R the genuine reference and then Q₂ can be chosen deep enough above
**all** primes of *positive or negative* odd vₚR that
vₚ(W_s)≥max(0,ceil(−3vₚR/2)), with the requisite extra depths at 2,3,17
and the old compact real preparations. Then b_s has square reduced denominator;
at untargeted primes v(b_s) is even. The compact bounds |Z_i|<2¹²,
0<|F|≤1/7 and R>2²⁰ give 0<b_s<2¹⁰⁰/R⁵<17. The scalar pole is thus
freshly realized, not carried across from an incompatible pole formula.

The scalar point is Q₂=[a₀']P₀ with a₀' chosen sufficiently large and
divisible by 3 along its allowed progression. Set **Q₁=[z]P₀**, not [β]P₀,
and keep the two actual Lucas-labelled points Q₃,Q₄. The independent scalar
control on Z and F involved H,Q₂, not a false [β]P₀ identity for Q₁.
Both Q₁,Q₂ are nonzero doubles with the true required shifts ≥7 and ≥9.
Freeze all denominators, root multipliers including z, scalar neighborhoods,
and the 30 distinct translated marks FIRST. The identical fixed-data thirty
Gaussian-prime supplier permits an arbitrarily large cutoff, slope and common
denominator divisibilities with pmax≤5pmin/4. At either split slot the order of the **full reduced elliptic group** is a
multiple of four by its rational 2-torsion and is (Hasse) <2pmin. Every
individual reduction order divides this group order; none can contain a
selected prime since the only possible positive multiple in that interval
would be the odd prime itself. Thus the old equal-depth CRT
preserves all earlier moduli while returning H to the prescribed scalar and
real neighborhoods. The two true signed role-one ratios have label z on the
chosen branches; all mixed factors are 1 on the successful slot, with inverse
residue 0 or 1 opposite. Each true comparison b_j has valuation one at its ten
selected primes, square reduced denominator, and the old small-place and real
limits. All three comparison poles and the actual scalar pole admit the four
independent rational realizations. Fill the finite-point charts, aggregate
rows and interpolation helper, then apply the invertible gauge. This produces
a full rational zero, without asserting that an arbitrary old 180/181 solution
can be transformed into one.

**Premises.** Precisely the donors' actual rank-one elliptic group and true-point
interpretations, formal and ordered real/finite returns, prepared rational pole
realization and odd-denominator obstruction, compatible fixed-data thirty-prime
progressions, Lucas estimate, original H4.1 and the effective four-point
full-field height. No unconditional theorem, minimal arity or Lean kernel
acceptance is asserted. See the independently reviewed fixed 180 source and
fixed181 source for the detailed common parts; neither previous literal changes.
