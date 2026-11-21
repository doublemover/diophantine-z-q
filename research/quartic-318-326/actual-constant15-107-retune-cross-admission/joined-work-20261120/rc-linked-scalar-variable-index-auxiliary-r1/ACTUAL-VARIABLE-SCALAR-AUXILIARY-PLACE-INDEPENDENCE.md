# Independent auxiliary local choices for the original a=0 scalar

This produces new permissible individual scalars, not a statement
about the earlier fixed h,J or a source of global rational points.
Keep \(a=A_{\rm label}=B_{\rm label}=0\), the original
anchor exponent \(N_0=65536\), and the same coefficients
\[
 \beta=204618888056724185,\quad R=4376874610839020,\quad
 A=114444R=17\cdot144\beta,\quad M=1+A,\quad K=6^{15}3^{N_0}.
\]
Use exactly the original label \(s=1+KJ\) (free \(d=1\))
and its actual Lucas labels. Write \(i=s-1\).
For the same raw original chart \(U_h\) and fixed source generator
\(R_0=(1+\sqrt2,2\sqrt2)\) on \(y^2=x^3-(3-\sqrt2)^2x\),
the literal scalar is
\[
 N_{\rm pack}=\mathrm N(1+U_h^2/R),\quad
 Q_{\rm pack}=R^{-15}\mathrm N(U_i/U_h),\quad
 W=N_{\rm pack}^2+R Q_{\rm pack}^2,\quad
 c=12W/M,\quad b=17\beta c^2,\quad D=\beta c^2,\quad
 \delta=1-D,\quad F=49D-48 .
\]
Here \(\mathrm N\) is the norm from \(\mathbf Q(\sqrt2)\).
If \(c=C/Z\) is reduced, \(H=Z^2\delta\), \(L'=Z^2F\).
None of the packed data is replaced as a rational value by
its residue.

## One independent CRT variable at each auxiliary place

Let \(S_0\) be the fourteen old places (2,3, all primes of
\(\beta\), and 13,37,53,131). At any finite set of auxiliary
odd primes \(p\notin S_0,\ p\nmid42RM\beta\), choose permitted
residues \(m\bmod p^2\), as specified below. Take a positive
formal center \(h_b\) divisible by the old exact center and
by \(p\) times every residue order of \(R_0\) at these new
places (both orders in the split case). At these primes
\([h_b/p]R_0\) is formal and multiplication by p gives
\(U_{h_b}\) depth at least two in every completion. They have
good reduction and are unramified in \(\mathbf Q(\sqrt2)\).
At 2 the original ActualOrbitBranchDepth318.two_u_place and
ActualOrbitCoefficientDepth318.two_chart remain in force
since \(64\mid h_b\). All old formal bounds, including the
depth-two bound at 131, survive taking multiples.

Set \(i=m h_b\) for the moment. In the formal parameter
\(z=-x/y\), \(U(z)=-2z+O(z^2)\) and \([m]z=mz+O(z^2)\)
with integral coefficients. Since \(v(z)\ge2\) and \(-2\)
is a unit, \(U_i/U_{h_b}\equiv m\bmod p^2\) before taking
norms, even if m is not a unit; the denominator is nonzero
by the original source nonzero norm. Hence, literally,
\[
 Q_{\rm pack}\equiv m^2/R^{15},\quad
 N_{\rm pack}\equiv1,\quad
 \boxed{W\equiv1+m^4/R^{29}\pmod{p^2}} .
\]
At each old place \(q\in S_0\), impose
\(2v_q(m)\ge15v_q(R)+1\) to retain the donor's positive depth
of \(Q_{\rm pack}\) and old W units. Use the original two-adic
norm valuation and the good unramified odd formal logarithm
as in the fixed scalar donor; no new prime-depth condition
on these old places is needed. At 131 this still gives
\(W\equiv1\bmod131^2\). Require also \(K/\gcd(K,h_b)\mid m\).
These divisibilities involve only old primes and are prime to
all selected auxiliary squares. CRT chooses one positive m.
Set one \(J=m h_b/K>0\), fix all original labels, and keep
\(i=KJ\) from now on. No assertion about **every** free \(d\)
is made: this is existence with \(d=1\).

With these fixed labels, ScalarIndexContinuity318.actual and
LocalIndexRegularity318.nat_progression keep all actual
\(W\bmod p^2\) neighborhoods and old units on one progression.
This applies also if W is zero modulo an auxiliary p; the
actual rational denominator \(H_{\rm chart}R^{15}\) is nonzero
and continuity does not require W to be a unit. Run
JointSmallPrimePreparation318.adjust_center inside this
progression for the real margin, actual guards and final
positive \(h>1\). It is **not** necessary that \(h\mid i\)
at the adjusted h: the congruence was proved at \(h_b\) and
transported with i fixed. AllScalarDetectorJoin318.join can
next retain the same modulus while preparing its three small
prime neighborhoods; no subsequent Gaussian pattern, full
four-pole tuple, or point is constructed here.

## Which choices are available

For the residue polynomial put \(w=1+m^4/R^{29}\),
\(c(m)=12w/M\), \(\delta(m)=1-\beta c(m)^2\) and
\(F(m)=49\beta c(m)^2-48\). A nonzero root mod p of
one of \(c(m),\delta(m),F(m)\) makes the other two
units. Its derivative is a unit: \(c'=48m^3/(MR^{29})\)
and the other derivatives are \(-2\beta c c'\) and
\(98\beta c c'\), with \(c\ne0\) in these latter cases.
The lift \(m=\mu+pt\) can prescribe any nonzero first unit
of the vanishing quantity. Since c is integral, Z is a unit,
so these are genuine depth-one possibilities for \(C,H,L'\),
not just raw valuations. To get a restrictive C row also
require \((3\beta/p)=+1\). An odd-depth L' row is restrictive
in either splitting case. A quiet mode, when accessible,
keeps all three functions units and gives the chosen
square/nonsquare character of \(\delta\), hence of the actual
\(\theta=\operatorname{sf}(\delta)\), at p.

There are arbitrarily many auxiliary primes allowing all
three depth-one choices. Use the fixed finite normal splitting
field of the three polynomials with denominators cleared,
adjoining \(\sqrt{3\beta}\) and any further fixed quadratic
splitting restrictions desired. The polynomials have nonzero
constants at \(m=0\) and only simple roots in characteristic
zero by the derivative check. Outside finitely many primes,
complete splitting gives all the required nonzero roots and
the C splitting condition. Infinitude does not need a density
estimate: a prime outside the discriminant with a root of the
minimal polynomial of a primitive algebraic integer of a normal
field splits completely. Indeed Frobenius at the corresponding
degree-one prime fixes a root, hence the primitive generator,
since the reductions of the roots are distinct. A nonconstant
integer polynomial has roots mod infinitely many primes:
otherwise put \(B=f(0)\prod_{p\in P}p\) for the finite prime
list \(P\), translating so \(f(0)\ne0\). For sufficiently large t,
\(f(Bt)/f(0)\) is an integer of absolute value >1 but is 1
modulo every prime in P, a contradiction. This is a production
theorem on finite *admissible* lists, not one for a preassigned
prime lacking the nonzero-root requirement.

## Five actual choices at one positive h, p=107

The exact fixed rational arithmetic control keeps
\(h=50674423719228247645312320\) in all five cases. The
inert residue point over \(\mathbf F_{107^2}\) has exact
order 106. This h is divisible by the original exact center
and \(107\cdot106\). The exact outward interval for
\(\mathrm N(U_h)\) is
\([-627103582363511543,-627103582363511542]/2^{64}\);
the source uses the **absolute** \(1/100\) margin. The
actual four guards at 5 have residue coefficients
\((4,1,1,1)\) as in the old witness: \([h]R_0=O\)
there, \(5\mid i\), and the Lucas labels reduce to
\((3723,1,-1,1)\) modulo 5. Thus no final continuity
or real adjustment is needed for these five samples.
PreparedIntegerSource318.scalar_domain gives the exact
positive \(b<17\), with the old scalar unit donor intact.

| mode | m mod 107² | W | c | δ | F |
|---|---:|---:|---:|---:|---:|
| quiet square | 1 | 5114 | 7729 | 1256 | 7151 |
| quiet nonsquare | 7 | 2986 | 7871 | 339 | 6288 |
| depth-one C | 9217 | 9523 | 107 | 1 | 11401 |
| depth-one H | 7429 | 8153 | 3405 | 107 | 6207 |
| depth-one L' | 4070 | 2994 | 3222 | 8643 | 107 |

All columns after m are modulo \(107^2\). Exact individual J
values and the common h appear in EXACT-VARIABLE-P107.json.
The checker reuses the old finite group and real directed
interval donor; it checks the literal elliptic order, common
h, guards, real margin, old divisibilities and one-prime CRT
perturbation. The two quiet rows yield opposite unit
characters of \(\delta\). The C type is restrictive because
\((3\beta/107)=+1\); the L' type is restrictive by odd depth
even though \(107\equiv3\bmod4\).

**Scope.** These are different allowed scalars with the same
original coefficients, prescribed local units, anchor branch,
real margin and actual guards. No retention of the old fixed b
or its 6551,83,or other incidental local rows is claimed.
No bound on extra moving support, hidden factor of the old H,
complete fixed global cover, or rational-point decision follows.
