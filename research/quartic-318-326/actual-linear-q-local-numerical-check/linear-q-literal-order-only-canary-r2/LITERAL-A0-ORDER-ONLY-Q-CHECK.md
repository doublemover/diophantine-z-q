# The literal a=0 detector at an actual order-only denominator prime

**Scope.** This is a numerical check of the new \(q\)-place handoff on all
three original poles and the same actual retained labels and scalar
progression, not a numerical simultaneous-prime key or a PointPair.
It replaces the old singleton's *role* of 3162001 (an incident contact)
by the linear route's denominator prime. It does not reuse that
singleton's \(q^3\)-divisible index.

Use the exact \(J\) of the archived \(a=0\) prefix (5a70adc6…) and
the explicit admitted Lucas pair of the shared-detector prefix a7dd144b….
Writing \(i=6^{15}3^{65536}J,\ s=1+i,\ k=2(s-2)\), the literal tuple is
\[
 (3723,s,U_s(k+1),U_s(k)/(s-2)).
\]
The recurrence is \(U_s(0)=0,U_s(1)=1,U_s(n+2)=sU_s(n+1)-U_s(n)\).
The calculation reduces these exact labels by binary matrix powers
modulo each actual half-point order, with \(s-2\) a unit in both
computations. It does not change them, approximate their sizes, or
claim to inspect an opaque choice. Let \(L\) be the exact augmented
retention modulus of the old singleton (modulo the original prepared
scalar/detector progression and additional certified scalar residues).
The checker pins those inputs and certifies the following concrete data.

* \(q=3162001=1065^2+1424^2\) is prime, Gaussian ray \((9,0)\bmod16\),
  \((1,3)\bmod7\), \(q\equiv1\bmod408\). The signed quarters are
  \(M_-=789968\), \(M_+=791033\). The primary and opposite exact
  half-point orders are 98746 and 791033, respectively.
* \(\gcd(M_-,L)=16,\ \gcd(M_+,L)=\gcd(M_-,M_+)=1\) and \(q\) divides
  none of these moduli. Take \(h\equiv H_{\rm retained}\pmod L\),
  \(h\equiv0\pmod{M_-}\), \(h\equiv1\pmod{M_+}\), \(h\equiv2\pmod q\).
  The least nonnegative CRT representative is positive and passes the
  strict actual scalar real norm guard, with outward interval
  \([-5594090724143263253,-5594090724143263252]/2^{64}\).
  At 5 the original four guard residues are unchanged.
* The **actual** formal parameters modulo \(q^2\) on the two formal
  arms are \(2383092645666\) for \([h]R\) (primary) and \(2063151898483\)
  for \([h-1]R\) (opposite), so both are exactly depth one. Neither
  \(h\) nor \(h-1\) is a multiple of \(q\).
* On each other arm where a ratio is not formally expanded, its base
  and four label multiples reduce to the signed original \(R,n_jR\)
  rows. The checker gives all nonzero \(U,V\), then the nonzero literal
  \(P_G,Q_G\) at \(D_{\rm curve}U(R)^4\) and \(Q_J\) at the three
  nonfirst \(V(n_jR)-1\), using Pade21Domains (not the older quadratic
  denominators). Replacing the nonformal \(R\) by \(-R\) changes only
  the sign of \(U\). Consequently the original formal and nonformal
  ratio inputs are simultaneously integral.
* The literal scales \(c=(1,\Re Z+N Z,NZ)\),
  \(Z=\prod_j(-1/U(n_jR))\), reduce to
  \((1,2129462,2940673)\), all units. The calculation uses both
  embeddings and the genuine common \(Z\). These are the unsquared literal
  \(\mathrm{ThreeDetectorUniformFamily318}.c_j\); the square is
  already in \(T=c_j^2t\).

For every rational \(t\) with \(v_q(t)=-1\) the five fixed roots are
integral at \(q\). Thus the actual \(T=c^2t,\Delta=T-1,F(T)\) have
valuations \(-1,-1,-5\). The weighted depths at literal slots
151,156,158 are exactly \(3,3,3\). The checked integral coefficients
above and the 16 steps \(X\mapsto X^2+\text{weighted leaf}\), starting
at 1, force both folds to 1 modulo \(q\). The actual trace quotient
\(\tau=N(X)/(2\Re X)\) satisfies \(2\tau\equiv1\pmod q\).
This is the order-only proof on the same charts and retained index,
with explicit residue values rather than a statement about a dummy
elliptic orbit.

The original pole formula, equivalently the expansion in the exact
shared-detector donor, now gives
\[
 v_q(b_{190},b_{241},b_{292})=(1,1,1),\qquad
 (b_j/q)\bmod q=(4c_j^{12}(qt))^{-1}.
\]
For the pointed local target \(qt\equiv1\), the three actual
unit residues are \(2371501,1890761,1500117\) modulo \(q\).
For example \(t=(q+1)/q\) is an exact rational representative
of this local cell; no assertion about its other places or its
real detector range is made. The same cell can be prescribed in a
linear-q datum \(t=u/(D^2Q^2q)\), \(v_q(DQ)=0\), by the single
congruence \(u\equiv(DQ)^2\pmod q\). This specifies the \(q\)-cell,
not existence of actual allowable primes in all contact forms.

## Test before any numerical full-key search

For a **proposed full key** at these exact labels, write \(B=DQ\).
A row difference at the root \(-1\) reconstructs
\[
 \frac{p_{j,-1}-u}{q}=m_j^2,\qquad m_j=B/|c_j|>0.
\]
Since \(D^2/c_j^2\) is integral (the \(-1\) root), \(D/c_j\) and
\(m_j\) are integers, not just rounded scale values. The remaining
literal forms of the same row must be *exactly*
\[
  (u,\ u+m_j^2 q/2,\ u+m_j^2q,\ u-m_j^2q/2399,\
        u+32m_j^2q/407).
\]
In particular \(2\cdot407\cdot2399\mid m_j\);
\(m_0=B\) since \(c_0=1\); and the ratio of the \(-1\) differences
in any two rows must be a rational square. These tests are necessary
without expanding any gigantic chart. For a positive key additionally
check the equalities \(|c_j|m_j=B\) against the actual chosen \(J\)
and labels, then primality/ray and all original CRT/real guards.
Passing only the rows or the displayed local canary is not a full
linear-q Ready or rational witness.
