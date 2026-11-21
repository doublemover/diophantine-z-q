# Linear Gaussian prime forms suffice for the same original Ready poles

**Paper alternative for the original 318/326 forward arithmetic.**
It produces the same three detector Ready inputs and the scalar
Ready input with the original labels and a single original CRT
index. It does not produce a numerical key, Lean proof, rational
PointPairs, or the final quartic. The additional denominator
prime has odd exponent in the contact parameter; this is not
an inhabitant of the old square-key Pattern structure.

## One exact linear key

Fix the original integer input, its nonzero fixed labels, clearing
\(D>0\), scalar and detector preparation \(h_0\bmod L\) with
\(64\mid h_0,L\), scales \(c_j\ne0\), and the five roots \(\theta_i\)
of the literal \(F\). Put \(k_{ji}=-D^2\theta_i/c_j^2\in\mathbb Z\)
and merge exactly equal coefficients \(k\), not detector rows.
For a fixed positive integer \(Q\) to be chosen before any
primes, and an extra rational prime \(q\), put
\[
 t=\frac{u}{D^2Q^2q},\quad p_k=u+kQ^2q,\quad
 F(c_j^2t)=\left(\frac{c_j^2}{D^2Q^2q}\right)^5
                 \prod_{i=0}^4 p_{k_{ji}} .
\]
The genuine prime forms \(q\) and the merged \(p_k\) have
pairwise nonparallel linear parts, and \(u=p_0\) is prime.
Take the rectangle \(3N/4\le u\le7N/8,\ \tau N\le q\le2\tau N\),
with \(\tau>0\) fixed sufficiently small. All contact primes
are then in \([0.7N,0.95N]\), distinct positions have spacing at
least \(Q^2\tau N\), and \(q\) is much smaller than any of them.
Since \(t\ge3/(8D^2Q^2\tau)\), this rectangle can be placed
above the old real threshold, fixed before prime selection.

## The exact full Gaussian ray has positive enough mass

Require every genuine prime, including \(q\), to have an
actual Gaussian representative \(\pi=a+bi\) of that norm
with \((a,b)=(9,0)\bmod16,\ (a,b)=(1,3)\bmod7\) and
\(N(\pi)=1\bmod408\). Fix a base prime set \(S_0\) containing
2, 3, 7, 17, the primes of \(L,D\), fixed scales, nonzero roots,
root-minus-one numerators, nonzero slope differences, all
local exceptional primes specified below, and an initial finite
interval larger than the number of forms and the needed sieve
threshold. Use the indicated residues at 2 and 7, and
\((a,b)=(0,1)\) at other odd base primes. The latter has
norm 1 and both translated norms 2; at 7 the norm is 3
and the translated norms are 2 and 6. This gives an actual
nonempty full base ray with both translated norms units
at every odd prime of \(L\). Norms are 1 modulo 8, 3, and
17, hence 1 modulo 408.

For each fixed cutoff \(s\) including the base, take the
Gaussian ray class field of modulus 16 times the product
of the odd base and cutoff primes. It is normal over
\(\mathbb Q\). The prime selector is the finite union of
rational conjugacy classes represented by a Gaussian unit
residue in the stated base branch and avoiding both translated
zero norms at every new wheel prime. Gaussian ideal classes
are trivial, so the kernel over \(\mathbb Q(i)\) is the
product of the finite unit rings modulo diagonal Gaussian
units. Being in the union means the rational prime has
at least one actual Gaussian representative with exactly
these requirements, not an average over independent signs.
Let \(F_0\) be the conductor of the maximal rational-abelian
subfield of the base ray field. Choose \(Q\) divisible by
\(F_0\), supported at the fixed base primes, and sufficiently
deep at every fixed denominator prime to meet the bounds
below. Thus on the base conductor all \(p_k\) are \(u\),
and \(u,q\) may independently have the same acceptable
unit residue. This does not set \(q=0\) on the fixed wheel.

At a new odd \(\ell\) the norm-one subgroup of the finite
Gaussian unit group, supported solely at \(\ell\), injects
in the ray group: a diagonal unit trivial at the base
mod 16 is identity. It lies in the rational Galois
commutator subgroup by writing its elements as \(x/\bar x\)
(finite Hilbert 90, or the split two-component formula).
The kernel of the base projection and all new local norm
maps is the product of these subgroups. The commutator
projects onto the base commutator, so modulo commutators
the base restriction and all new local norms suffice.
At the new primes the abelian conductor exponent is
at most one because the new Gaussian ray inertia is tame.
This proves the independent norm-one variation in each
conditional class fiber with the base branch kept. In a
unit norm fiber there are \(\ell-\chi_4(\ell)\) possible
residues. In the split coordinates \(xy=n\) translated
norm zero forces one coordinate to be \(1\) or \(-1\),
thus removing at most four points. Inert removes at
most two. With \(r\) genuine forms the new local density
is at least its ordinary linear prime factor times
\((1-4/(\ell-\chi_4(\ell)))^r\). The ordinary factor is
positive and \(1+O_r(\ell^{-2})\), since the distinct
zero lines in two variables meet only at the origin.

Apply the unconditional [Frei–Tinková, v3 Theorem 1.4
and formulas (1.10), (1.15)](https://arxiv.org/html/2408.17441v3#S1.SS2)
to these fixed nonparallel linear forms and the convex
rectangle, classwise summed over the finite union. There
is one fixed positive base factor, and the product of
the new losses is bounded below by a fixed negative
power of \(\log s\), using \(\sum_{\ell\le s}1/\ell
=\log\log s+O(1)\). The genuine prime mass with one
actual \(\log p\) per form is consequently
\(\gg_\tau N^2/\sqrt{s}\) for large \(N\) at each fixed
\(s\). Proper prime powers contribute only \(o(N^2)\):
one form has \(O(\sqrt N\log N)\) such values and at
most \(O(N)\) preimages per value, before the fixed
log powers. No moving-field uniformity is asserted.

## Ambient four-variable upper, not a rank-six quadric

Use the independent Descent paper A4-SIEVE-FOR-PRIME-STEP
(c30ce02259b5f143d67dd289418b2a35a51bef1dd7234f70a2f2b1e967fd07e4)
on these exact forms and phase rectangle. Two distinct
Gaussian prime forms, including \(q\) if needed, determine
\((u,q)\) uniquely from their two norms. This injects
every cross-position bad key into a Gaussian integer
four-box of side \(O(B)\), \(B=\sqrt N\). For an
opposite-sign event at one position, pair it with any
second distinct form; reconstruction still holds. It
is an upper bound even if witnesses are not unique.
All observed norm values and shift norms are positive,
and actual prime outputs prohibit a zero coordinate
real part in the same-position divisibility argument.

The packing bound is \(O(B^4/Y)\) unweighted at an
odd prime above \(Y\): in each translated isotropic
residue lattice nonzero squared distances are divisible
by the prime, hence the spacing is at least its square
root. The same-position event forces the real coordinate
divisible by the prime and the imaginary coordinate
a root of \(x^2+1\), with eligible primes no greater
than the coordinate bound. The log-weighted large
bound is therefore \(O(B^4(\log B)^r/Y)\).
For medium primes \(\ell\), the bad residue set has
\(O(\ell^2)\) classes in four coordinates. Eliminating
the key gives two rank-two prime norm polynomials and
the other rank-four linear combinations of the two
norms, with union density
\(g(p)=(r+2\chi_4(p))/p+O_r(p^{-2})\) away from
fixed minors. CRT gives the local main term times
\(|\Omega_\ell|/\ell^4\) and the explicit error
\(O(B^3 d/\ell)\) for auxiliary squarefree \(d\)
coprime to \(\ell\), \(\ell d\le B\).
The elementary ambient Selberg diagonalization gives
\(G_\ell(z)\gg(\log z)^r\), with coefficients
\(|\lambda_d|\le d\), uniformly after omitting one
\(\ell\). Take \(z=Y=B^{1/20}\); weighted medium
obstructions then cost \(O(B^4/s)+o(B^4)\).
This upper counts true primes retaining the **same**
once-counted \(r\) logs as the lower, and imposes
no uncontrolled conditional Gaussian distribution
on the medium range.

Choose \(s\) sufficiently large **after fixing** \(\tau,Q\),
then take \(N\) sufficiently large at that fixed \(s\).
The medium upper and power-saving large upper are
smaller than the true lower mass. All smaller odd
prime obstructions were deleted by the full ray.
One key with actual Gaussian representatives survives
\[
 \gcd(N(\pi_i-1),N(\pi_j+1))=4
\]
for every ordered pair including equal positions and
the order-only \(q\). The 2-part is exactly 4 from the
stated mod-16 residues. This uses no large-incidence
independence assertion, no PET, and no quadric
equidistribution input.

## The same original CRT index, with q order-only

The original per-prime Gaussian ray, actual Jacobi
count, orientation and quarter-order arguments apply
to the extra \(q\) too: their per-prime versions take
the actual Gaussian representative, residue roots,
and stated mod-7 character. They produce the exact
two signed counts and the original **half-point**
residue order dividing each corresponding quarter,
not the order of a surrogate point. Let \(M_-,M_+\)
be the LCMs of the signed quarter counts for all the
positions, including \(q\). Let \(\Pi\) be the product
of the **contact primes only**.

The original five compatibility conditions follow.
Cross gcd-four gives \(\gcd(M_-,M_+)=1\).
Odd avoidance and the mod-16 signs give
\(\gcd(M_+,L)=1,\ \gcd(M_-,L)=16\); the large prime
cutoff gives \(\gcd(\Pi,L)=1\). For
\(\gcd(\Pi,M_+)=1\), the old separation argument among
the contacts uses the bound \(1+2\sqrt N\) on neighbor
error versus linear contact spacing and their common
size band. At the same contact the plus norm is even
and strictly between 0 and \(2p\), so it is not \(p\).
At \(q\) its plus norm is smaller than every contact
prime by the choice of \(\tau\). There is **no requirement**
that \(q\) avoid divisibility of another plus norm,
because \(q\) is absent from \(\Pi^3\).

The original ThreeDetectorCRTWitness318.prepared_family
takes arbitrary rational \(t\) and exactly these CRT
conditions. It chooses one \(h>1\) with
\(h\equiv0\bmod\Pi^3M_-\), \(h\equiv1\bmod M_+\),
and \(h\equiv h_0\bmod L\), with the same original
real region, signs, guards, source rows, and
\(0<b_j<17\) at all three detector poles. The original
scalar real range and scalar readiness are unchanged
and independent of \(t\).

## Literal local glue at q and all other places

At a contact prime the exact factor product gives
\(v_p(F(c_j^2t))=1\) in each incident row, and
\(c_j,\Delta_j=c_j^2t-1\) are units. These use just the
fixed cutoff, distinct within-row factors, and
root-minus-one numerators, not a global square class
of \(t\). The original \(p^3\) and opposite order
conditions yield all the original positive primary
leaves and the opposite valuation bound. Their
prime-local calculation uses the actual parameter
only through the three weight valuations
\(-1,-7,-25\), exactly as in the original trace proof.
Thus the literal poles have valuation \(+1\) at
all their contact primes. This is reuse of the
prime-local calculation, not an application of its
old square-key wrapper.

At the new prime \(q\), the same index has \([h]R\)
in the formal subgroup on the primary arm and
\([h-1]R\) in it on the opposite arm. **Depth one
suffices here.** The original primary ratio estimate
at formal depth one and the original alternate
Padé ratio estimate on its formal disk make their
respective ratios integral. The nonformal primary
charts on the other arm reduce to the fixed
\(R,n_jR\) charts; the nonformal alternate charts
likewise reduce to the fixed \(-R,-n_jR\) charts.
The finitely many fixed nonzero-multiple charts
are regular after deleting a fixed set of primes.
The required denominator values are nonzero by
the original chart-domain formulas and the actual
\(h=2,\ h-1=1\) common-log identity; replacing \(R\)
by \(-R\) changes the sign of \(U\) only. Deleting
their fixed numerator and denominator primes
makes these divisions integral and preserves
their reductions. This set is fixed before choosing
\(q\); no denominator depending on a later \(h\)
has been silently excluded.

The first two literal unweighted leaves use the
norm of \(U(h)\) and the components of
\(f_V=U(h-1)^2\). The remaining leaves use the
eight \(U,V\) charts and the two sets of original
ratios by polynomials with fixed rational
coefficients. This follows by substituting the
literal fills in PadeRatioWitness318,
DetectorGateWitness318 and ActualDetectorFold318.
Thus all coefficients are integral in both arms;
their rational coordinates are integral since
\(2,\sqrt2\) are units. At this \(q\),
\(v_q(T)=-1,\ v_q(F(T))=-5,\ v_q(\Delta)=-1\),
and the three weight depths are exactly
\(3,\ 7\cdot3-18,\ 25\cdot3-72\), all 3.
Both folds are 1 modulo \(q\) and the literal
trace quotient is a unit. Hence
\[
                         v_q(b_j)=-5-6(-1)=1 .
\]
The nonsquare denominator of \(t\) causes positive,
not negative, odd depth of each original pole.

At all fixed denominator primes enlarge \(Q\) so
each \(v_p(c_j^2t)\) is negative even and strictly
below the root valuations, simultaneous in \(j\).
The five factor valuations are then even, hence so
is the pole valuation by the literal square factor.
Outside the fixed denominator primes and the selected
ones, the exact factor product has even valuation
(in fact is a unit with the chosen cutoff). Nonzero
poles follow from the real domain. This proves square
reduced denominators of the three actual \(b_j\).

At \(2,3,17\), \(q\equiv1\bmod408\) is a local square.
Put \(d_p=DQ\sqrt q\) in the respective local field.
Approximate \(d_p\) by rational integers \(d\)
multiples of \(DQ\), by approximating the local
unit square root with integers. The original
SourceLocalProgression318.Prepared is syntactically
for \(u/d^2\), and applies to these approximants:
the five normalized factors
\(u-\theta_i d^2/c_j^2\) are integers, nonzero square
units because \(u\equiv1\bmod408\) and \(Q\) was fixed
sufficiently deep, and the same index satisfies
\(h\bmod L\). The literal rational pole expression
is continuous in \(t\) at the target: its required
nonzero denominators are supplied by the original
compact real domain. The set of squares including
zero of at least the required valuation is closed
locally; pass to the limit, preserving the exact
nonzero pole and original minimum depth. This proves
the same local Ready data. No global \(d\) with
\(t=u/d^2\) was asserted.

## What this replaces, and what it does not

| Old square-key obligation | Linear denominator-prime route |
| --- | --- |
| True prime mass for \(u+c_i w^2\), weighted PET and ordinary affine joining on the original nonlinear carrier | Direct unconditional affine-linear Artin prime theorem for fixed nonparallel forms, full rational Gaussian ray |
| Primitive rank-five quadric counts and medium/large neighbor sieves on that quadric | Exact reconstruction from two norms in the ambient 4-box, elementary Selberg and lattice packing |
| Global square contact denominator in the trace wrappers | Fixed even saturation, local square approximation at \(2,3,17\), and positive \(q\)-valuation using the order-only prime |
| One original h, real open region, CM orientation and actual trace leaf identities | Kept unchanged, except \(q\) added to both quarter LCMs and **not** to \(\Pi^3\) |
| Actual simultaneous ranks, marked rational points, row-287 anchor, and final source consumer | Unchanged and not supplied by this paper |

PreparedIntegerSource318.complete_at_index consumes
arbitrary rational \(t\), the exact original source
rows, the real guards, four literal PointPairs on
these same poles, and the original row-287 anchor.
No square-denominator hypothesis on \(t\) occurs
there. This paper reaches the same four Ready
premises; a genuine rank or point supplier is still
needed. It uses the existing original finite/local
preparation, elliptic orbit and literal trace/CM
lemmas as mathematical inputs. It does not change
any theorem to an axiom or mark any Lean scope green.

Exact selected source pins (SHA-256 prefixes):
ClearedContactForms318 1ed66c70;
ThreeDetectorCRTWitness318 837caa15;
PreparedIntegerSource318 e3ecec83;
SourceLocalProgression318 cd5f09f0;
ActualAlternateRatioPrecision318 48606002;
ActualSourceRatioParameters318 d670034b;
ActualPrimaryLogPrecision318 d2c6bc48;
ActualDetectorFold318 1bb3b85f;
ThreeDetectorArithmetic318 6afbbd9c;
GaussianQuarterModuli318 f2c36cd8;
SelectedQuarterOrder318 de0a4151;
CanonicalSelectedCounts318 0fdaf3f9.

Signed: independent reviewer / paper route author, with
Descent's independent ambient upper proofs and controls,
2026-11-21 UTC.
