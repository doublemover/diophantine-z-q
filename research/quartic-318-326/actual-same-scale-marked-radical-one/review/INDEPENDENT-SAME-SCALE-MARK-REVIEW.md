# Independent cold review: actual same-scale two-factor marked radical

Signed: independent mathematical reviewer, 2026-11-21. PASS on the
exact paper proof, conditional endpoint as stated; no Lean execution.
The author packet is `linked-detector-same-scale-odd-mark-r1`
manifest 70410179d9e116b8c39b8f19c8afc2a4434d267caf6b863fd37cf0841c0d565e,
proof 27babd0d1f21e57853400351cf664f2a8c61b90b6d011d4ebe35e8aba4cc88b4,
checker f40b9560326fc913e325d58ce23bff5d67f0460c705efe4f9471be992c75b314,
result 83e54b5e4d087577596f80462955fa1563e0ce85cbd3783ca7f39e10b73c2d16.
I verified the author's manifest and replayed the entire result byte-for-byte
with the five original contact JSONs. Three independent finite controls
accompany this receipt.

**Original contact and selection.** I recomputed both c1-scaled factors
at the same w mod p^2 at each of the sixteen inherited primes. Only the
negative factor hits the included p_a, with literal value p_a mod p_a^2;
the positive same-c1 factor is a unit at every inherited ball. In particular
p_b=9807649 is an arithmetic order pilot only: the old positive c2 ball
remains at p_b exactly, and is not a support prime for b=q1*q2. Its primary
and opposite orders 2453441 and 29, with the indicated arm, fit the literal
XVI anchor; their group counts are 9813764 and 9801536 with gcd 4. The product
of q1 and q2 norm characters is set at the old balls; at both p_a and q_a
it must be negative because s-t is a nonsquare. Taking q1 negative and q2
positive at both makes a=p_a*q_a square at both new primes by reciprocity,
as required by t-s being square at their selected orientation. The q1/q2
mutual sign is positive. Hensel at a unit square root of t supplies the
new exact depth-one factor cells without altering the other equation.
All preceding h constraints survive the two finite prime selections:
the order levels strip old contacts, and every detached prime has
both group counts a unit, independently of the depth of its old CRT
condition. The same odd common-order finite-plus-tail sieve works for
each newly fixed finite compositum. Its short tail uses disjoint abelian
Gaussian rays outside the finite ramification set; its long tails do
not require uniform Chebotarev in that compositum. The final even
progression invokes the established fixed-source real-density lemma.
At B the old saturated regime still has both support classes locally
square, and the good-place smooth genus-one argument supplies the
remaining local points. These are simultaneously retained local
requirements, not a rational point in their intersection.

**Full Selmer image, not a selected subspace.** The square-scaled roots
are S=-74955737824 and T=397391951, with
T-S=407*2399*3^2*5^2*7^3. The support is complete from this literal
factorization and the four moving primes. Good odd primes allow just
unit classes; nonsplit depth-two at 3 also allows only units, since a
point near the two colliding roots either has equal smaller depth and
the forbidden nonsquare leading term, or has minimum depth two and
even parity in both differences. At 5 the split collision gives
square first coordinate; at 7 the nonsplit odd-depth collision gives
first unit sign equal to the common collision-depth parity. Each is
an equality by the four-element odd local Kummer image. At 11,37,2399
and the four moving primes the rational torsion rows have distinct
valuations and exhaust that same local image. At 2 the product x(x-S)
is square when v2(x)<=2, while x-T is directly square when v2(x)>=3;
the torsion points and x=S+640 give classes 2,-1,10 and exhaust the
eight-element group. The middle coordinate at the real place is
positive. Triviality at q2 exactly removes the two independent
torsion Kummer directions. Independently, I built 29 linear rows
on 20 input bits directly from these conditions and from the
multiplicative torsion-root formula. Their rank is exactly 17; the
three displayed literal F,U,V are a basis. The raw marked triple
(D,b,a) follows from x=D*w^2, y=D^2*w*U0*V0 and normalizes to F
by the rational t-root torsion class. There is no rational point
of order four: a local moving prime already distinguishes every
nonzero torsion Kummer row by valuation.

**All three Cassels bits.** I checked [Smith, Theorem 3.2 and proof,
especially (3.3)](https://arxiv.org/pdf/1607.07860#page=13).
The base comparison curve is the true E_(a*q1); its full rational
2-torsion identifies the constant coefficient module on both
q2 twists. Fixed places include infinity, 2, fixed bad primes
and prior moving support, where the twist ratio is square. The
three fixed normalized basis classes are in both Selmer groups
and trivial at their respective q2. The class group condition for Q
is empty. Hilbert 90 supplies the F2-valued cup primitive; Smith's
quadratic-character correction removes extraneous ramification.
On the common quadratic-cocycle kernel the primitive is additive.
For tame inertia iota, evaluation on (iota,iota) gives
Gamma(iota^2)=e2(F'(iota),G'(iota)); its image is central in the
governing field. The recorded valuation rows at p_a,11,2399 give the
three independent shifts (100),(010),(011) on (FU,FV,UV).

The order field is unramified at each of these detached places except
its abelian Gaussian rays. In particular stripping 11 and 2399 from
the original positive pilot's prime-to-residue torsion and division
levels is crucial; imposing both group counts units thereafter is
strictly stronger than the removed order caps. Their changed phases
need preserve only the rational squareclass, not the full Gaussian
congruence. For an explicit independent check, at inert 11 choose
tame generator 4+i: the residue 10+9i goes to 1+6i after square
multiplication, and neighbor norms change (8,4) to (3,7), all units
mod 11. At inert 2399 choose 5+i: (658,680) goes to (1795,1309),
counts (1621,1854) to (1972,1955) mod 2399. At split p_a use
primitive 3 in the first component: (2,2) goes to (18,2), with
counts (1,9) and (17,57). The two norm phases have the required
unchanged square character in every case and avoid every forbidden
fourth root of unity. These are residue controls, not purported
global primes. Frobenius can be multiplied by the three central
square images in the actual common compositum, not just in separate
quotients: all cocycle fields are fixed, while only the appropriate
detached ray coordinate changes. The old finite Gaussian coprimality
conditions and positivity of Chebotarev's main term survive. Choosing
the alternating bits (0,0,1) makes the ordinary normalized radical
precisely the actual line generated by F.

**Arithmetic limit.** The radical is the image of Sel4 in Sel2
modulo the actual rational torsion plane. Its dimension is the full
2-primary Selmer corank plus the even dimension of twice the
4-torsion in the finite reduced 2-primary Sha. Therefore the corank
is 1 unconditionally; no Sha finiteness is assumed at this stage.
As a separate check, the same-scale base root sign is -1 (only 5
is split among the extra places 3,5,7), also giving odd full
2-primary corank via rational 2-isogeny parity. I read the
[version-pinned October Theorem 1.1](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-October-7-2026/build/sections/introduction.tex#L12-L42):
this E_D has the specified rational 2-torsion and full corank 1 and
is in its stated scope. Its use here is explicitly an external
preprint premise, not an independent proof audit. On that premise,
rank one means the unique normalized radical is the rational point
line; a rational torsion adjustment gives the exact raw ordered mark.
The two equations then share one finite rational w: at infinity a
and b are nonsquares, w=0 is excluded by the positive t equation,
and zero ordinates would require a rational square equal to negative
s or to t of squareclass 2399. This supplies no numerical q or h,
no rational point in the prescribed product of local balls, no
other root factor, no PointPair, and no formal Lean result.

## Independent replay

    python3 -B check_independent_kummer_matrix.py | cmp - INDEPENDENT-KUMMER-MATRIX.json
    python3 -B check_independent_inertia_rays.py | cmp - INDEPENDENT-INERTIA-RAYS.json
    python3 -B check_independent_old_phases.py TRIAD.json SIX.json XII.json XIV.json XVI.json | cmp - INDEPENDENT-OLD-PHASES.json
    sha256sum -c SHA256SUMS
