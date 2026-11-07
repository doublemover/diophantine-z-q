# Arithmetic derivations

The 318-variable source uses the constructions below. Its final parameters are local orders 4 and 13, scalar index 8, contact-height exponent 49/8, and fixed integer S = 3^(2^16). Earlier parameter choices in the derivations are specialized by the final height and exceptional-prime bounds.

- [Current compressed anchor, integer labels and scalar soundness](#compressed-anchor)
- [Real-part guards and completeness bounds](#real-guards)
- [Kato applicability and the remaining global dependency](#kato-scope)
- [Historical reciprocal H,V0 charts and exact fixed translation](#reciprocal-fixed-translation)
- [Affine parity packing in the existing semilocal anchor](#affine-parity-anchor)
- [Rational V0 norm test and the exact base-detector weight rewrite](#norm-v0-orientation-and-base-weight)
- [One-gate odd-input encoding](#odd-linear-square-input)
- [Linear delta leaves in the reciprocal norm chain](#parity-even-linear-delta-leaves)
- [Eliminate the remaining detector p-square helpers](#pole-first-square-rescaling)
- [Branch-controlled reciprocal logarithms](#reciprocal-log-branch-rescue)
- [Removing scalar preparation after fixed correction and half-norm packing](#scalar-preparation-zero)
- [Six-helper order 8/29 weights, including the new zero branch](#six-helper-8-29-trivial-height)
- [Square-root Kummer scalar translation for the V10 branch](#square-root-kummer-scalar)
- [Shifted square-root product height scales](#square-root-product-height-scales)
- [Cusp-coordinate estimates used in the final height argument](#cusp-coordinate-estimates)
- [Direct finite-place bound without the modular-degree factor](#direct-divisor-finite-bound)
- [Finite exceptional-prime refinement for the 318-coordinate source](#finite-exceptional-primes)
- [Contact-height exponent 49/8 by metric cancellation](#height-49-over-8)
- [Vertical branch support for the Gamma_H cover](#modular-vertical-support)
- [Formal-log and Padé accuracy outside primes at most17](#small-prime-log-tail)

<a id="compressed-anchor"></a>

## Current compressed anchor and torsion-safe scalar comparison

This supplement applies to the literal 318-variable source in `construction/318/build_source.cjs`, especially the fixed-anchor rows at lines 408–425 and the scalar rows at lines 817–845. It supplies connecting arguments for those rows. It does not replace the inherited elliptic-group theorem, pole-obstruction theorem, or global height theorem.

### Reconstruction of the compressed anchor

Put

\[
K=\mathbb Q(\sqrt2),\qquad d=3-\sqrt2,\qquad D=d^2,
\qquad E:y^2=x^3-Dx.
\]

Write the fixed point as \(P=(k^2,km)\), with the actual nonzero constants

\[
k=-1+\frac74\sqrt2,\qquad m=\frac{39}{8}-\frac92\sqrt2,
\qquad m^2=k^4-D.
\]

The compressed source has \(f,w\in K\), \(n_H\in\mathbb Q\), and the relations

\[
F:=1-k^2f(1+w^2)-2mfw-Df^2w^2=0,
\qquad n_H^2=N_{K/\mathbb Q}(f).
\tag{1}
\]

The assigned auxiliary values are \(t=fw\) and \(f_V=fw^2\). Define

\[
A=m+(Df+k^2)w,\qquad B=k^2+mw+Dfw^2.
\]

Direct expansion using \(m^2=k^4-D\) gives

\[
fA^2-k^2(1-Df^2)=-(Df+k^2)F,
\tag{2}
\]
\[
fB^2-k^2(1-Df^2w^4)=-(Dfw^2+k^2)F.
\tag{3}
\]

First, \(f\ne0\), since otherwise \(F=1\). Hence \(n_H\ne0\). Also \(A\ne0\): by (2), \(A=0\) would give \(f=\pm1/d\), whose norm is \(1/7\), contrary to (1), since \(1/7\) is not a rational square. If \(w=0\), then \(B=k^2\ne0\). If \(w\ne0\) and \(B=0\), (3) gives \(fw^2=\pm1/d\), so

\[
\bigl(n_H N_{K/\mathbb Q}(w)\bigr)^2=1/7,
\]

again impossible. Thus both denominator expressions \(A,B\) are nonzero throughout the actual source domain.

Define

\[
H=\left(\frac1f,\frac{A}{kf}\right).
\tag{4}
\]

For \(w\ne0\), define

\[
V_0=\left(\frac1{fw^2},-\frac{B}{kfw^3}\right),
\tag{5}
\]

and for \(w=0\), define \(V_0=O\). Identities (2) and (3) prove that these are points of \(E(K)\). Their finite ordinates are nonzero.

These points satisfy the exact, oriented group relation

\[
H-V_0=P.
\tag{6}
\]

For \(w\ne0\) and \(w^2\ne1\), the slope of the line through \(H\) and \(-V_0\) simplifies to

\[
\ell=\frac{y(H)+y(V_0)}{x(H)-x(V_0)}
=\frac{k^2+mw+(Df+k^2)w^2}{kw}.
\]

Substitution of \(F=0\) gives

\[
\ell^2-x(H)-x(V_0)=k^2,
\qquad -y(H)+\ell(x(H)-k^2)=km,
\]

which proves (6). The equal-abscissa cases are not discarded. For \(w=1\) or \(w=-1\), equations (4)–(5) give \(V_0=-H\). Substitution into the tangent formula

\[
\ell_{\mathrm{tan}}=\frac{3x(H)^2-D}{2y(H)}
\]

gives \(\ell_{\mathrm{tan}}^2-2x(H)=k^2\) and
\(-y(H)+\ell_{\mathrm{tan}}(x(H)-k^2)=km\). Thus \([2]H=P\), again proving (6). The nonzero ordinate already established makes the tangent formula legitimate. Finally, when \(w=0\), (1) gives \(f=1/k^2\), so \(H=P\) and (6) holds with \(V_0=O\).

With \(z(Q)=-x(Q)/y(Q)\) for finite non-torsion points, and \(z(O)=0\), the actual source expressions are therefore

\[
z(H)=-\frac{k}{A},\qquad z(V_0)=\frac{kw}{B}.
\tag{7}
\]

In particular the primary ratio row is exactly \(z(U_i)/z(H)\). The common alternate logarithm is \(z(V_0)\) times its stated rational \(G\)-approximant. The latter is zero precisely in the \(V_0=O\) branch, using the separately established global nonvanishing of its numerator and denominator. This reconstruction does not itself remove that exceptional ratio branch; the later local/height argument must retain its stated treatment.

#### Completeness of the compression

For the original completeness witnesses, take finite nonidentity \(H\in2E(K)\) and \(V_0=H-P\). Let \(f=1/x(H)\). Since \(x(H)\) is a square, choose \(u_H\in K\) with \(u_H^2=f\), and set \(n_H=N_{K/\mathbb Q}(u_H)\). Put

\[
w=\frac{kf\,y(H)-m}{k^2+Df}.
\tag{8}
\]

The denominator is nonzero: at either real embedding \(f>0\), \(D>0\), and \(k^2>0\). With this choice \(A=kf\,y(H)\); the elliptic equation and (2) imply \(F=0\). Equations (4)–(6) then recover the original \(H,V_0\), and (1) holds. Thus the completeness witnesses lift through the compression using rational coordinates. This is a completeness lifting statement, not a claim that every compressed witness has a square abscissa.

### The exact free label and the remaining torsion coset

Use the inherited assertions

\[
2E(K)=\mathbb ZP,\qquad [2]R_0=P,\qquad E(K)_{\mathrm{tors}}=E[2](K),
\]

where \(R_0=(\epsilon,2\sqrt2)\), \(\epsilon=1+\sqrt2\), and \(E[2](K)\) is generated by \(T_0=(0,0)\) and \(T_d=(d,0)\). The established squareclass homomorphism satisfies

\[
\alpha(m_0R_0+aT_0+bT_d)
=[\epsilon]^{m_0}[-1]^a[d]^b,
\qquad a,b\in\{0,1\},
\tag{9}
\]

and \(\alpha(Q)=[x(Q)]\) when \(x(Q)\ne0\). These are the group and squareclass inputs recorded in the [Version 9 addition](../../../docs/quartic-523-540/addition.tex), lines 382–388, and the [pinned Version 10 manuscript](sources/quartic_v10.tex), lines 19475–19500.

For the reconstructed \(H\), equation (1) implies that \(N(x(H))=1/n_H^2\) is a rational square. Taking norms of the squareclass identity (9), and using

\[
N(\epsilon)=-1,\qquad N(d)=7,\qquad N(-1)=1,
\]

shows that \((-1)^{m_0}7^b\) must be a rational square. Therefore \(m_0\) is even and \(b=0\). Consequently the actual source has

\[
H=hP+\tau,\qquad V_0=(h-1)P+\tau,
\qquad h\in\mathbb Z\setminus\{0\},\quad \tau\in\{O,T_0\}.
\tag{10}
\]

Here \(h\ne0\) because (4) is finite with nonzero abscissa and nonzero ordinate, excluding both \(O\) and \(T_0\). In particular the exact norm-square source does not require half-integer free labels. The equal-abscissa possibilities above are actually excluded once (10) is used: \([2]H=P\) would imply \(2h=1\).

The torsion term \(\tau\) must not be omitted. If \(\tau=T_0\), then \(x(H)=-D/x(hP)\), which is negative at both real embeddings. Thus neither \(H\in2E(K)\) nor real positivity of \(f\) is available for arbitrary soundness witnesses. Whenever logarithms compare \(H\) with a point \(R=cP\), use the exact identity

\[
[2h]R=[2c]H,
\tag{11}
\]

which kills \(\tau\). There is no need to assert the potentially false identity \([h]R=[c]H\).

### Scalar divisibility without a real-sign assumption

Let the preceding scalar Kummer reconstruction supply a finite nonidentity point \(R=cP\in2E(K)\), with signed label \(c\in\mathbb Z\setminus\{0\}\). Write \(f_R=1/x(R)=u_R^2\), \(n_R=N(u_R)\), and keep \(n_H^2=N(f)\) as above. The literal scalar rows impose

\[
N=N_{K/\mathbb Q}(1+f/r)
=1+\frac{2f_0}{r}+\frac{n_H^2}{r^2},
\]
\[
Q=\frac{n_R}{n_Hr^{15}},\qquad
W=N^2+rQ^2,\qquad
b=c_0r\left(\frac{W}{1+c_0r}\right)^2,
\qquad c_0=114444.
\tag{12}
\]

The exponent is 15, not 16: the emitted `ri16` numerator is divided by `scalarScaledNormH=n_H/r`. All displayed quotient domains follow from the retained inverse equations, the anchor reconstruction above, and the separately established input squareclass argument for \(1+c_0r\).

Fix a consumed contact prime \(p\notin S_{\mathrm{bad}}\), and suppose

\[
R_p:=v_p(r)>0\quad\text{is odd}.
\tag{13}
\]

In particular \(p\) is odd, \(K/\mathbb Q\) is unramified at \(p\), the elliptic curve has good reduction, and \(D,c_0\) are units. Normalize each local valuation \(\nu_v\) above \(p\) by \(\nu_v(p)=1\). If \(d_v\) is its residue degree, then

\[
v_p(N_{K/\mathbb Q}(a))=\sum_{v\mid p}d_v\nu_v(a),
\qquad \sum_{v\mid p}d_v=2.
\tag{14}
\]

Only the soundness direction of the inherited pole theorem is used here: the pole predicate excludes negative odd values of \(v_p(b)\). Since \(1+c_0r\) is a unit and \(Q\ne0\), the summands \(N^2\) and \(rQ^2\) have unequal even and odd valuations, with the usual value \(+\infty\) allowed for a zero first summand. Thus \(W\ne0\). Its pole argument has odd valuation

\[
v_p(b)=R_p+2v_p(W)\ge1,
\]

so \(v_p(W)>-R_p/2\). Noncancellation in \(W=N^2+rQ^2\) then gives

\[
v_p(N)>-R_p/4,\qquad v_p(Q)>-3R_p/4.
\tag{15}
\]

For any non-torsion point of \(E(K_v)\), the valuation of its abscissa, and hence of its reciprocal abscissa, is even. Indeed, if \(\nu_v(x)<0\), the curve equation gives \(2\nu_v(y)=3\nu_v(x)\); if \(\nu_v(x)>0\), it gives \(2\nu_v(y)=\nu_v(x)\); valuation zero is immediate. Therefore \(\nu_v(f)\) is even and cannot equal the odd number \(R_p\). It follows that

\[
\nu_v(1+f/r)=\min(0,\nu_v(f)-R_p)\le0.
\tag{16}
\]

The norm in (14) is a sum of these nonpositive valuations. Its lower bound in (15) forces every summand in (16) to exceed \(-R_p/4\). Hence

\[
\nu_v(f)>3R_p/4>0\qquad\text{for every }v\mid p.
\tag{17}
\]

Thus \(H\) is in the formal group at every place above \(p\). This conclusion holds on the \(T_0\)-coset too; it does not use the sign of any real coordinate.

From the second inequality of (15) and (12),

\[
v_p(n_R/n_H)>\frac{57}{4}R_p\ge\frac{57}{4}.
\]

The left side is an integer, so it is at least 15. Since

\[
(n_R/n_H)^2=N_{K/\mathbb Q}(f_R/f),
\]

we obtain \(v_p(N(f_R/f))\ge30\). By (14), at least one place \(v\mid p\) has \(\nu_v(f_R/f)\ge15\). Both reciprocal-abscissa valuations are even, so at that place

\[
\nu_v(f_R/f)\ge16.
\tag{18}
\]

Equations (17)–(18) make both \(R\) and \(H\) formal there. At an unramified good odd place the formal logarithm is an isometry on this formal group, and for a formal point \(T\),

\[
\nu_v(\log_E T)=\nu_v(z(T))=\tfrac12\nu_v(f(T)).
\]

Applying the logarithm to the torsion-safe identity (11) gives

\[
\frac{\log_E R}{\log_E H}=\frac{c}{h},
\qquad
v_p(c/h)=\tfrac12\nu_v(f_R/f)\ge8.
\]

The nonzero formal points have nonzero logarithms; \(h\ne0\) was established above. Finally \(h\in\mathbb Z\) implies \(v_p(h)\ge0\), and therefore

\[
p^8\mid c.
\tag{19}
\]

This supplies the scalar-index order 8 conclusion needed by the subsequent contact-height argument. It is a local soundness proof and applies equally at split and inert primes through the residue-degree weighting in (14). It does not claim an order proportional to \(R_p\); the contact radical needs the fixed order 8 for each consumed prime.

#### Real completeness remains a separate use

The existing completeness construction chooses \(H\in2E(K)\), hence \(\tau=O\), and lifts by (8). Its positive real reciprocal chart and the associated smallness estimate for \(W\) remain available for that chosen family. No such positivity assertion is needed or justified for arbitrary soundness witnesses on \(\tau=T_0\).


<a id="reciprocal-fixed-translation"></a>

## Historical reciprocal H,V0 charts and exact fixed translation

This section records the earlier square-chart construction with translation 4P. The final builder instead uses the free-f compressed chart with translation P; its current reconstruction, integer label and torsion treatment are given in the [compressed-anchor bridge](#compressed-anchor). Do not apply the earlier H=4P exceptional-branch conclusion to the final rows.

### Two quadratic field equations

Choose fixed k,m0 in K with k nonzero and

    R0=4P*=(k^2,k*m0),   m0^2=k^4-D.

Such constants exist because R0 is a nonidentity point of 2E(K); they can be obtained from the explicit doubling formulas and checked exactly.

Give H and V0 independent reciprocal charts

    H=(u,v), V0=(a,b),
    v^2=1-Du^4, b^2=1-Da^4,
    fH=u^2, fV=a^2.

As in the companion note, u=0 or a=0 represents O. Encode the fixed group relation by only

    k*v = m0*u + k^2*a + D*fH*a,
    k*b = -m0*a - k^2*u - D*u*fV.

These are quadratic field equations because fH,fV are already assigned. No inverse of fV-fH is used in this fixed-translation block.

### Algebra and absence of hidden denominators

Set B=k^2+D*u^2. Under either real embedding D>0 and k^2>0, so B>0 and in particular B is never zero. The first equation gives the unique value

    a=(k*v-m0*u)/B,

and the second then uniquely determines b, since k is a nonzero constant.

Let

    E3=1-2*m0*u*a-D*u^2*a^2-k^2*(u^2+a^2).

Squaring the first translation equation, using v^2=1-Du^4 and m0^2=k^4-D, gives B*E3=0. Therefore E3=0. Substitution into the two displayed rows then gives

    k*a*v+m0*u*a+k^2*u^2-1=0,
    k*u*b-m0*u*a-k^2*a^2+1=0.

When u,a are nonzero, put h=1/u, A=1/a, m=v/u^2, n=b/a^2 and lambda=(h*A-m0)/k. The three resulting identities are

    m=h*lambda-A*k,
    n=h*k-A*lambda,
    lambda^2=k^2+h^2+A^2,
    m0=h*A-lambda*k.

These are the complete Jacobi difference equations. They imply H-V0=(k^2,k*m0), including the tangent cases h=+/-A. On the ordinary secant chart this follows by substitution in the usual group law; at h=+/-A the equations force the true tangent and exclude the equal-point/infinite-difference case because the target k is nonzero.

The identity boundaries have the correct orientation, with no extra sign branch:

- If u=0, then v=+/-1, a=v/k and b=-m0*v/k^2, so V0=-R0.
- If a=0, then b=+/-1, u=-b/k and v=-m0*b/k^2, so H=+R0.

Both identities cannot occur. Thus this is an everywhere-defined exact translation on the reciprocal chart, not merely an abscissa relation or an unguarded secant quotient.

### H cannot be O in the full source

The tiny scalar certificate contains

    Norm(fH) * normalizedNormRatio = Norm(fS) * rInverse^128.

The right side is nonzero: the source retains rInverse, and Norm(fS) is an inverse of the nonzero positive root norm. If H=O then fH=0 and the left side is zero, a contradiction. Hence the full source still has H nonidentity, without an extra guard.

### V0=O is a valid exceptional soundness branch

If V0=O, the exact translation gives H=4P*, so its integer label is h=4. The equations defining the LP_i quotients have zero denominator and force each numerator log_trunc(V_i) to be zero. The reciprocal logarithm is zero only at O: its denominator v is always nonzero, and for nonidentity points the inherited global nonvanishing of G_J and z applies. Therefore every V_i=O and Q_i=U_i.

The LP_i coordinates may now be arbitrary. They are NOT used to recover labels in this branch. Instead, at every relevant detector contact prime, the order-one tests make H and U_i formal. The denominator label h=4 is a p-adic unit, and the ordinary one-anchor truncation estimate gives

    L_i congruent to 4*u_i/h = u_i = n_i

with the required precision. This is a local congruence, not an assertion that truncated ratios equal integer labels globally.

The later height transfer, Lucas contradiction, scalar height estimate, and beta comparison use only the recovered congruences and the unchanged actual root labels/heights. They never divide by h-4 in this branch. Therefore the existing soundness argument continues unchanged after this separate comparison lemma. No additional V0-nonzero guard is needed.

When V0 is nonidentity, the usual two-anchor proof applies exactly as before. Completeness retains the original large positive h and therefore never needs the exceptional h=4 branch.

### Dependency scope

The proof uses the established square-abscissa interpretation of 2E(K), the inherited reciprocal-logarithm nonvanishing/truncation statements, and the existing arithmetic source. It adds only explicit field identities and a separately stated comparison case. It does not establish the deeper arithmetic assumptions of the original claimed construction.

<a id="affine-parity-anchor"></a>

## Affine parity packing in the existing semilocal anchor

### Scope

This is an arithmetic source transformation of the pinned V10/523 construction at commit ba7a3e0a0c171b7cd2ce75976addba57fad8a5dd. It retains the inherited arithmetic hypotheses. It does not constitute a formalization or independent verification of those hypotheses. The proposed source removes the four odd-coset chart augmentations and replaces the existing semilocal anchor and one height scale. The compiler must establish the actual coordinate count.

Primary source: `docs/quartic-523-540/addition.tex`, especially the fixed-point, product-height, scale, odd-chart, and shifted-scalar sections. The builder is `quartics/quartic-523-540/source-reproduction/builders/odd-product-asymmetric-source.cjs`, which transforms `odd-product-source.cjs`.

### Notation

K = Q(sqrt(2)), d = 3-sqrt(2), D = d^2. The curve is E: y^2=x^3-Dx. The generator of 2E(K) is

P=((57-28sqrt(2))/8,(-660+417sqrt(2))/32).

All four finite nonidentity root points are Q_i=[n_i]P, with nonzero integer n_i; this already follows from their square-abscissa charts, before imposing oddness. Put C=product_i x(Q_i)=C0+C1sqrt(2), and T=2^24 Norm(C).

The scalar point is R=[a-1]P, finite and nonidentity in the original 523 source. Write f(R)=f0+f1sqrt(2). The old physical anchor parameter is A=f0^2+f0*f1-f1^2. Its fixed scale is S0=3^(2^26). Its three-witness conic is equivalent to A/S0 being integral at both 2 and 3.

### Exact 2-adic parity detector

Use the extension of v2 normalized by v2(2)=1. From the displayed coordinates, v2(x(P))=-3 and v2(y(P))=-9/2, so v2(z(P))=3/2, where z=-x/y. This is in the formal-logarithm isometry region v2(z)>1. Therefore for every nonzero integer n,

v2(z([n]P))=3/2+v2(n),
v2(x([n]P))=-3-2v2(n).

The unique place above 2 has local degree two, so

v2(Norm(x([n]P)))=-6-4v2(n).

Consequently

v2(T)=-4 sum_i v2(n_i) <= 0,

with equality exactly when every n_i is odd. No cancellation occurs in this multiplicative identity.

The old anchor A/S0 is always 2-integral, without the oddness conditions. Indeed R is a nonzero integral multiple of P, and v2(f(R))=3+2v2(a-1)>=3. If f=f0+f1sqrt(2), the two summands have valuations v2(f0) and v2(f1)+1/2, which are distinct whenever both are nonzero. Thus their minimum is v2(f), and both rational coefficients are 2-integral. The polynomial A is then 2-integral, and S0 is a 2-unit.

### 3-adic behavior once oddness is known

The prime 3 is inert in K, the curve has good reduction there, and P reduces to a nonidentity point of order two with unit x-coordinate. Thus every odd multiple of P reduces to that same point and has 3-adic unit abscissa. When all n_i are odd, Norm(C), and hence T, is a 3-unit.

### Replace the physical anchor affinely

Set Anew=A+S0*T. The new conic tests

Anew/S0=A/S0+T

for integrality at 2 and 3.

At 2, A/S0 is integral. If v2(T)<0, the summands have unequal valuations and their sum has negative valuation. Hence the new 2-condition forces v2(T)>=0, which is equivalent to all four labels being odd. Once this has been proved, T is 3-integral, so the new 3-condition is equivalent to the old 3-condition. The old 2-condition holds automatically. Conversely, the old anchor plus odd labels implies both new local conditions.

This proves equality of the projected rational source domains: the new anchor replaces the old anchor plus the four odd-coset chart conditions. The three conic witness coordinates may change; no literal identity of those witnesses is asserted. Existence in either direction follows from the same exact semilocal characterization used by the source.

The affine expression A+2^24*S0*Norm(C) needs no new coordinate when A and Norm(C) are assigned. Its square remains quadratic in those coordinates. The symbolic constant remains S0, but the anchor residual now contains S0^2*Norm(C)^2, so its sum-of-squares quartic can have S0-degree four instead of two. The exact coefficient maximum must be recomputed. A small-coefficient lift treating S0 as a coordinate needs additional helper assignments; the upstream 17-coordinate lift cannot simply be reused.

The same argument applies to the later half-norm scalar anchor: its parameter Norm(u_R)/C_anchor is automatically 2-integral, and replacing its physical numerator by numerator+C_anchor*T preserves the threshold. It does not require the numerator to be positive.

### Height scales sharing the norm coordinate

Replace the old scales 1,C0^2,(1+C1^2)^2 by 1,C0^2,Norm(C). Since every x(Q_i) is a nonzero square in K, C is a nonzero square, so Norm(C) is a positive rational square. At both real embeddings x(Q_i)>=d_embedding, hence Norm(C)>=7^4. Also C0>1. All fixed-scale, positivity, and prime-selection requirements continue to hold.

Suppose the unchanged detector estimate bounds the heights of both nontrivial scales by 2T0, where T0=(H+log(3))*|N|^(19/k). Then h(C0)<=T0 and h(Norm(C))<=2T0. The monic polynomial

Z^2-2C0 Z+Norm(C)

has C as a root. The standard coefficient/Mahler-height bound gives

2h(C)<=h(1,-2C0,Norm(C))+log(3)
       <=3T0+log(2)+log(3).

This deliberately uses a conservative log(3) error. The resulting bound h(C)<=1.5T0+0.5log(6) is below the existing 7H*|N|^(19/k) bound for H>=1. Thus the V9 product-height identity, once oddness has been recovered from the anchor, gives the same root-height inequalities and the same numerical soundness constants.

This does not claim that the norm alone controls C. The C0^2 scale is retained, so split-prime cancellation in the norm causes no gap.

### Nominal circuit saving

- Remove four odd charts: 16 rational coordinates and 16 quadratic residuals.
- Replace C1^2 and (1+C1^2)^2 by a single Norm(C) assignment: one further coordinate saving.
- Keep C0^2 and the original physical A assignment.
- Replace A by Anew only as an affine expression in the anchor residual and metadata.

Nominal total saving: 17 coordinates, subject to exact compiler replay and independent coefficient audit.

### Stronger implementation using the product of square roots

When the root chart supplies h_i with x(Q_i)=h_i^2, form Kprod=product_i h_i=k0+k1sqrt(2), so C=Kprod^2. Put n=Norm(Kprod). Then Norm(C)=n^2, and the parity detector can be replaced by

Tprime=2^12*n.

Indeed v2(Tprime)=-2 sum_i v2(n_i), and at 3 it is a unit once all root labels are odd. Its sign is irrelevant. The same affine anchor proof therefore applies with Tprime instead of T.

This permits a more efficient height circuit. Assign n=k0^2-2k1^2 and m=k0*k1. The scales are

Norm(C)=n^2,
C0^2=n^2+8m^2.

Both can remain raw quadratic expressions when introduced through reciprocal common-parameter equations mu*t=scale. The anchor uses n affinely, so it needs no Norm(C) assignment, even with the half-norm scalar anchor.

Multiplying four h_i in K costs the same six rational multiplication outputs as multiplying the four x_i. If A,T,Z root abscissas have no other consumers, their six assigned rational components can be removed. S's abscissa may remain for the scalar Kummer shift. The two new helpers n,m replace the two old scale helpers, so the nominal additional saving is six coordinates. This is an exact polynomial identity transformation; audit all root-x consumers before applying it.

With the standard translated anchor and a unit coefficient for n, its formal leading quartic coefficient becomes 9*2^56*S0^4. Exact primitive normalization and coefficient reconstruction must still be checked. A decimal fixed-constant lift needs a helper for S0*n, in addition to the usual chain.

<a id="norm-v0-orientation-and-base-weight"></a>

## Rational V0 norm test and the exact base-detector weight rewrite

### Replacing the alternate common-point membership test

Keep nH^2=Norm(f(H)), the rational nH test of order 11, every primary Ui formal-membership test, all four alternate Vi branch tests, all cross-comparisons and the Lucas residual.

Replace the order-one field test conjugate(f(V0)) by the rational test Norm(f(V0)), also of order one. The old conjugation does not matter for the norm. The unchanged norm-chain lemma now supplies both positive norm valuations at its selected good place, as well as all the other required test valuations.

#### The norms identify opposite formal places

At a split good prime, positive Norm(f(H)) implies H is formal at at least one of the two places. Positive Norm(f(V0)) likewise implies V0 is formal somewhere. They cannot be formal at the same place, since H-V0=P and P is nonformal at every consumed prime. Therefore they are formal at opposite places. At the other place each point reduces to +P or-P, respectively, and its f value is a unit.

At an inert good prime, positive norms would put both points in the same formal group, contradicting their difference P. Thus active inert contacts cannot occur. If V0=O globally, H=P and the nH test cannot hold at any good prime; the existing empty-contact/height exclusion of that branch remains valid.

#### Lucas forces the correct orientation

Suppose the norm-chain selected place were the one where V0 is formal. Then H reduces to P. Both x(P) and y(P) are units at every prime above76176, as

    Norm(x(P))=41^2/2^6,
    Norm(y(P))=3^2*7*17*41/2^9.

Thus z(H)=-x(H)/y(H) is a unit there. The retained primary Ui tests make every Ui formal, or equal to O. Hence each primary ratio L_i=z(Ui)/z(H) belongs to the maximal ideal, with zero allowed at O.

In particular L_S,L_T,L_Z all vanish modulo p. The direct Lucas residual

    L_T^2 - L_S*(L_S-2)*L_T*L_Z + (L_S-2)^2*L_Z^2 - 1

is then-1 modulo p. This contradicts its positive test order 41. The selected place must therefore be H-formal, and the opposite place V0-formal.

Now f(H) is a unit at the opposite place. The identity nH^2=Norm(f(H)) gives selected v(f(H))=2*v_p(nH)>=22. Therefore z(H) has depth at least11, the primary relative log error is at least44, and the existing11/41 comparison proof applies unchanged.

This orientation argument needs the primary S/T/Z membership tests. A later deletion of those tests requires a replacement argument; their omission is not covered here.

#### Completeness and gate count

The old completeness witnesses already have H formal at the selected place and V0 formal at the opposite place. Since V0 reduces to-P at the first place, its f value is a unit there; hence Norm(f(V0)) has positive valuation and satisfies the new order-one test. No new congruence or prime-pattern hypothesis is needed. The new rational function is bounded on the same compact real region after the old pole exclusions, so the existing continuity and preparation arguments apply.

The old field square f(V0)^2 is still needed by its G10 logarithm. Consequently it must not be counted as removed. Instead use the identity

    Norm(f(V0))^2 = Norm(f(V0)^2).

The right side is a rational quadratic expression in the two already assigned components of logV0.fSquare. Assign just that one test-square helper; keep the conceptual test value Norm(f(V0)) as a raw quadratic semantic expression.

Place this rational leaf immediately after the rational nH leaf. The second norm-chain node is then rational in every detector, so its zero imaginary output needs no coordinate. Three saved outputs minus one new global square helper give the measured net saving of two.

### Exact detector0 q1/e fusion

For detector0 the scale A equals1, so the existing equations imply

    e*F=delta^5,
    q1*delta^3=e,
    q1*F=delta^2.

Retain delta^2 and delta^3, replace the q1 definition by q1*F=delta^2, and assign e=q1*delta^3. Remove the separate delta^4 helper formerly used to compute e. The delta^2 expression already reuses Fsquare-2t+1.

The retained eInverse equation forces e nonzero. The new product definition then forces q1 and delta nonzero; q1*F=delta^2 forces F nonzero. Hence all old quotient domains reconstruct. Conversely every old witness satisfies the new equations. Restoring the old delta^4 helper as(delta^2)^2 gives the inverse witness map. This is an exact rational projection equivalence, not an arithmetic relaxation, and saves one coordinate.

### Rejected stronger V0 depth shortcut

Raising the rational Norm(fV0) test from order one to order eleven would force opposite-place V0 depth at least six. This would permit a shorter G2 logarithm polynomial in soundness. However, it breaks the generic completeness CRT: H depth eleven requires p^10 dividing h, whereas V0 depth six would require p^5 dividing h-1. These cannot both hold. The actual construction uses h=0 modulo the high contact-prime power and h=1 modulo the opposite reduction order, with that order prime to the contact prime. It supplies only the baseline opposite formal depth. The V0 test therefore remains at order one, and its G10 polynomial is retained. The evaluator independently checked this obstruction.

<a id="odd-linear-square-input"></a>

## One-gate odd-input encoding

Set

T=2X+1, A=3723=3*17*73,
beta=A*T²,
r=(beta-1)(beta-2401)(32beta+343)(2beta-1).

Retain correction11. If the preparation-zero scalar normalization is used, replace its fixed multiplier by c0=114444=4*11*9*17².

### Integral-input bridge uses the existing odd-root conclusion

A is odd and squarefree. If beta is an integer and T=a/b in lowest terms, b² divides A, so b=1. If beta is also odd, T must be odd, hence X=(T-1)/2 is an integer. Conversely, integer X makes T an odd nonzero integer and beta an odd integer at least3723>2401.

The source already proves that the recovered root label n is odd by the affine parity anchor. Its final conclusion beta=n therefore supplies exactly the oddness needed here. Integrality alone would not suffice, and must not be claimed to do so.

### The omitted contact

At every good prime p>76176, A is a unit and v_p(beta)=2v_p(T) is even. Thus the beta contact contributes no odd prime outside the cutoff, just as in the preceding square-input source. All other contacts are represented by r. Negative good valuations of r are even because r has degree 4 and v_p(beta) is even. Every consumed odd contact therefore has positive odd v_p(r).

The exceptional value beta=0 occurs at the rational input X=-1/2. It is not a zero of r. In that branch h(beta)=0 directly, so the scalar height estimate is automatic. The final equality beta=n with n odd excludes the branch. Do not invoke the five-contact height theorem at its omitted root0.

### Global2-adic domain proof

Global real positivity of r is no longer available for arbitrary rational X. It is replaced by an exact2-adic statement: neither -r nor -11r is a square in Q2.

For nonzero T write j=v2(T), beta=2^(2j)*B, where B is an odd unit with B=3 modulo 8. Direct factorization gives:

- j>=1: v2(r)=0, unit class1 modulo 8.
- j=0: v2(r)=2, unit class3 modulo 8.
- j=-1: v2(r)=-5.
- j=-2: v2(r)=-11.
- j=-3: v2(r)=-18, unit class3 modulo 8.
- j<=-4: v2(r)=8j+6, unit class1 modulo 8.

At T=0, r=-7^7 has valuation0 and unit class1.

For the negative strata put k=-2j and beta=B/2^k. The third factor has numerator2^5 B+343*2^k, with valuation min(5,k), since k is even. The last factor has numerator2B-2^k, with valuation1. Thus v2(r)=min(5,k)+1-4k. At k=6 the divided unit product is3; at k>=8 it is B^4=1 modulo 8. For j=0, both first factors have valuation1 and their divided units differ by 1200, a multiple of 8, so their product is square modulo 8; the remaining units give7*5=3. For j>=1 the first two units again multiply to a square and the remaining units give7*7=1.

In every even-valuation case, -r has unit5 or7, and -11r has unit7 or5. In the other cases the valuation is odd. Neither is a2-adic square. In particular r is never zero.

The packed scalar has W=N²+r*q² with q nonzero from its retained inverse/quotient equations. Hence W=0 would make -r a rational square, which is impossible. Therefore b=11rW² is nonzero. The old preparation denominator1+b*t² cannot vanish because -b has the nonsquare class of -11r. This recovers the old domain facts without assuming r>0.

For the normalized preparation-zero version,1+c0*r cannot vanish because c0 has squareclass11 and -11r is nonsquare. Thus its quotient is defined everywhere on the source domain. At every active good contact this denominator is also a unit, as before.

### Integer-input local classes and completeness

For integer X, T is odd and beta=3 modulo 8, beta=0 modulo 3 and modulo 17. The four-factor r is positive, exceeds10, and has:

v2(r)=2 with unit class3;
r=2 modulo 3;
r=5 modulo 17.

Correction11 is class3 at 2, class2 at 3, and class11 at 17; its products with these units are squares. The additional square4*9*17² gives c0*r valuations4,2,2 at 2,3,17, satisfying the same preparation-zero thresholds.

The existing finite preparation makes W a unit at every prime dividing c0*r. Therefore the reduced denominator of c0*r*(W/(1+c0*r))² is a square. The same positive-measure real choice gives W<2 and 0<b<4/(c0*r)<17. All old completeness steps remain available because beta is odd and larger than 2401 for every integral X.

The valuation-stratum argument above is the proof. The rational-input bridge is also formalized in the retained local Lean components.

### Implementation obligations

Replace the inputSquare/inputY/inputYSquare chain by beta=3723*(2X+1)². Keep correction11; an earlier tentative correction41 was based on mistakenly including the omitted beta factor and is not correct here. Keep the same four-factor r. In a prep-zero branch use c0=114444. Update all positivity/domain comments and the input bridge proof. The remainder of the detector, scalar norm, parity anchor, and Lucas source is unchanged.

<a id="parity-even-linear-delta-leaves"></a>

## Linear delta leaves in the reciprocal norm chain

### 1. Intrinsic valuation parity

At any good odd nonarchimedean place of K, let D be a unit and let u,v satisfy

    v^2=1-D*u^4,
    delta=v-1.

Then ord(delta) is even whenever delta is nonzero.

- If ord(u)<0, the term D*u^4 is uniquely dominant, so ord(v)=2ord(u)<0. Hence ord(delta)=ord(v)=2ord(u).
- If ord(u)>=0, then ord(v)>=0 and ord(delta)>=0. If ord(delta)=0, the assertion is immediate. If ord(delta)>0, odd residue characteristic gives ord(v+1)=0; from delta*(v+1)=-D*u^4 one gets ord(delta)=4ord(u).
- If delta=0, then u=0 and the leaf vanishes. Its valuation is infinity and causes no cancellation issue.

This holds at every good place, not only at completeness primes and not only on a chosen local branch. Conjugating the field pair preserves the statement at the conjugate place.

### 2. Generalized chain step

The chain step is W_j=W_(j-1)^2+q_m*L_j. Previously every L_j was a square. The proof needs only that its nonzero valuation is even, because q_m has odd valuation whenever the contact valuation R is odd. Thus there can be no tie with the even valuation of W_(j-1)^2.

For each of the four opposite variable-point membership tests, replace the old L_j=delta^2 by L_j=delta, with weight q1. All other leaf expressions and weights remain unchanged. At a consumed contact, ord(q1)=-R, R>0. The backward chain threshold gives

    ord(q1*delta)>-R/2,

and therefore ord(delta)>R/2>0. This is more than enough to force the desired v=+1 formal branch. Once positive, ord(delta)=4ord(u), so the existing direct J-log approximation applies with unchanged relative precision.

For negative odd R, every nonzero right term still has odd valuation. The initial left value1 still forces the terminal valuation to be at most0, so the same pole/trace argument excludes negative contacts. If the entire W vanishes, the same even/odd separation rules out every consumed odd contact, and the existing empty-contact branch applies. No assertion of global real positivity of arbitrary witnesses is introduced.

### 3. Completeness

Retain the old globally canonical duplication charts. At selected contact primes delta has arbitrarily high positive valuation on the forced branch. At the opposite place it is either zero, a unit or has even valuation, so the same chain induction gives W^-1 congruent to 0 or1. The selected-place value remains1, and the trace denominator remains a unit. At the finitely many small primes, replacing delta squared by delta changes fixed valuation thresholds only; the source permits arbitrarily deep congruence choices before choosing the large scaling parameter.

At both real embeddings delta lies in[-2,0]. The new right term can be negative, but its size is uniformly bounded by 2 times the small weight. The finite-depth chain still tends to 1 as the common positive scaling parameter tends to infinity. Thus all required nonzero values, real signs, square-denominator/pole preparations and finite-pole avoidance can be retained by increasing the scaling parameter. This is the same asymptotic completeness argument, with a different fixed constant.

### 4. Circuit implication

For Padé(2,1), the numerator P(delta) is quadratic and its denominator Q(delta) affine. Therefore the field quotient equation can consume raw delta squared without an assigned delta-square field coordinate. The four old assigned branch-square helpers are no longer needed by either the membership chain or the logarithm evaluation. The measured source saves eight rational coordinates,326 to 318, with 288 residuals and 3145 quartic monomials.

The emitted metadata must describe these four overrides as parity-even linear leaves, not as squared tests. No witness map claims delta=delta^2. The actual chain equations, Padé quotient equations and absence of the old helpers require an independent emitted-source audit before any final count is claimed.

<a id="pole-first-square-rescaling"></a>

## Eliminate the remaining detector p-square helpers

The normalized detector pole in the corrected343 source is

    17*b*p²=(17−e)(17+3e),
    H=e*(17−b), T=(s²−H)(s²+3H), 17*q²=b*T.

Replace the first witness by P=b*p. Its first equation becomes

    17*P²=b*(289+34e−3e²).

The apparent cubic can be rewritten using the already assigned H:

    17*P²−289b−578e+34H+51e²−3eH=0.

Every term is quadratic. Expanding H=e(17−b) verifies the identity exactly. The second pole equation and all its helpers remain unchanged. Thus the normalizedP2 assignment is unnecessary, saving one coordinate for each of the three detectors.

For b!=0 this is a birational change of the normalized first witness. A more useful comparison with the original unnormalized pole is

    old_p=P, old_e=b*e, old_s=b*s, old_q=b*q.

Substitution into the two original pole equations gives b times the new first equation and b³ times the new second equation, respectively. At b=0 the new equations force P=q=0 and still map to a valid original pole with old_e=old_s=0. Conversely, when b=0 an original pole exists and the new pole also exists by taking P=q=s=e=0. Hence the projection onto b is preserved even on the zero branch; no inverse guard or new arithmetic hypothesis is needed.

This is exactly the first-conic algebra already used in the scalar preparation-zero block. Applying it to detector poles does not import additional scalar completeness hypotheses: it is an algebraic existential equivalence with their old pole predicate.

<a id="reciprocal-log-branch-rescue"></a>

## Branch-controlled reciprocal logarithms

### The rejected shortcut

For the reciprocal chart x=u^-2, y=v/u³, v²=1−Du⁴, the invariant differential is −du/v. Near either point above O, write v=σ sqrt(1−Du⁴), σ=±1. The formal logarithm is

−σ u H(Du⁴),
H(w)=sum_{n≥0} binom(2n,n) w^n/[4^n(4n+1)].

Therefore replacing a logarithm by −u H_N without a branch condition is unsound. Independent chart choices can give either sign. This unguarded replacement is not part of the audited429/422 checkpoints.

### Sound repair

For the four alternate points Vi, replace their formal-membership test f(Vi) by v_i−1, retaining order 1. At an unramified good odd contact prime,

(v_i−1)(v_i+1)=−D u_i⁴.

The test v(v_i−1)≥1 makes v_i+1 a unit, forces u_i formal, and fixes σ=+1. The direct truncated polynomial −u_i H_N now has the correct sign. H10 has relative error44 and H2 has relative error12, sufficient for the mixed41/11 scheme. For Ui orVi=O the numerator is zero, so the absolute congruence is immediate.

The common denominator V0 may retain its existing G10 logarithm. Fuse −u_i H_N directly into the LP_i quotient numerator, omitting four intermediate logarithm outputs. Crucially, do not allocate fresh squares of v_i−1: the curve equation gives the exact identity

(v_i−1)²=2−2v_i−w_i, where w_i=Du_i⁴=Df_i².

The existing logarithm circuit already supplies w_i. This affine expression is the squared leaf for the symmetric detector product. Its use needs an explicit identity certificate rather than an undocumented syntactic replacement.

### Completeness from the existing Gaussian ray

The existing selected Gaussian primes obey π=a+bi≡9 modulo 16. Thus16 divides b and p=Norm(π)≡1 modulo 16.

Cox, Primes of the Form x²+ny², Theorem4.23 on p83, proves the quartic supplement (2/π)_4=i^(ab/2), equivalently the classical criterion that p=x²+64y² implies2 is a fourth power modulo p. Hence2 is a fourth power at every selected p.

A primitive16th root in Fp shows that both2+sqrt(2) and 2−sqrt(2) are squares. Because2 is a fourth power, either choice of sqrt(2) is itself a square; the sign does not matter since−1 is square. Therefore ε=1+sqrt(2)=(2+sqrt(2))/sqrt(2) is a square at both K-places above p.

Put R0=(ε,2sqrt(2)), so P=2R0. The three full2-descent coordinates of R0 are

x(R0)=ε,
x(R0)+d=4,
x(R0)−d=2/ε.

They are all squares in Fp. The standard full2-descent halving criterion therefore gives R0∈2E(Fp). The latter group has order d_±(p)/4. The existing congruence h−1=0 moduloM_plus consequently makes [(h−1)n_i]R0 formal at every opposite selected place, with no new CRT factor or prime-pattern assumption.

Choose the reciprocal chart of Vi by the rational duplication formula from T_i=[(h−1)n_i]R0:

u=2y(T_i)/(x(T_i)²+D),
v=(x(T_i)⁴−6D x(T_i)²+D²)/(x(T_i)²+D)².

When T_i is formal, this v reduces to+1. This supplies the required branch simultaneously at all selected contacts. The rational formulas are globally defined in completeness because x(T_i)²+D is positive at the real embeddings. The finite small-prime continuity conditions and real boundedness remain of the same type as in the inherited construction.

<a id="scalar-preparation-zero"></a>

## Removing scalar preparation after fixed correction and half-norm packing

The initial formulas in this section record the earlier nested-input, order-32 stage. The final source uses beta=3723(2X+1)^2, a=114444r and q=Norm(uR)/(nH*r^15). See the [current torsion-safe soundness argument](#compressed-anchor) and [final real bound](#real-guards) before applying these earlier calculations.

### Input and scalar notation

Use Y=102X^2+357, beta=Y^2, and

r=(beta-1)(beta-2401)(32beta+343)(2beta-1).

For integer X this is a positive integer greater than 10. The fixed squareclass correction 11 makes 11r square in Q2,Q3,Q17. Put c0=11*9*17^2=28611 and a=c0*r. Then a has local valuations v2(a)=6, v3(a)=2, v17(a)=2. These statements are proved in the separate odd-input audit. The same correction is a unit at every prime beyond the source's cutoff.

Let R be the scalar elliptic point (S-P in the completeness witnesses), and use the packed half-norm scalar with

N=Norm(1+fH/r),
q=Norm(uR/uH)/r^63,
W=N^2+r*q^2,

where fH=uH^2 and uR^2=fR=1/x(R). In a relaxed-H soundness chart, the equivalent norm-square formulas replace the literal uH; completeness can and does choose H in 2E, so these displayed expressions apply to the real and local construction below.

Define the new pole argument

b=a*(W/(1+a))^2.

Use the preparation-zero pole on this b.

### Soundness at the relevant contacts

The odd input beta is a rational square, so it has no negative odd valuation at a good prime. The omitted beta factor is also a square. Every odd contact contributing to the scalar five-contact radical is therefore a finite contact with v_p(r)>0 odd. At such a prime, c0 is a unit and 1+a is a unit. Thus

v_p(b)=v_p(r)+2v_p(W),

exactly as for the original pole argument. The existing pole obstruction and the complete packed half-norm valuation proof consequently give the same order-32 divisibility of the scalar point's index and the same height bound. No claim is made that this normalization preserves pole obstruction at unrelated negative valuations of r; none is needed by this input encoding.

It is essential that the denominator depends only on a=c0*r, not on W. The seemingly more convenient bounded map aW^2/(1+aW^2)^2 would turn forbidden negative odd valuations into allowed positive ones and is invalid for soundness.

### Small-prime and denominator conditions for completeness

For an integer input a is a positive integer, and gcd(a,1+a)=1. The unchanged scalar preparation chooses the scalar point and common point deep enough at all primes dividing a that W is a unit there; it may impose further arbitrary finite divisibility conditions. Therefore the reduced denominator of a*W^2 is a square, and dividing by (1+a)^2 preserves that property. More explicitly, at a prime dividing a, W and 1+a are units, so the valuation of b is nonnegative. At a prime not dividing a, its valuation is twice an integer, hence any negative valuation is even.

At 2,3,17, both W and 1+a are units. Thus b is a local square and has the same valuations 6,2,2 as a. These satisfy the preparation-zero thresholds v2>=3, v3>=1, v17>=2.

The unit condition on W at the support of a is necessary. Merely observing that a is integral and W/(1+a) is rational would not prove square reduced denominator.

### An explicit real bound for the packed norm

We can choose the common point H along every required arithmetic progression so that

|Norm(uH)| >= 1/(100*sqrt(7)).

Here is a quantitative justification. In either real embedding write d_sigma>1 and normalize the reciprocal chart by s=u_sigma*sqrt(d_sigma). Its equation is v_sigma^2=1-s^4. On the compact real identity component, the invariant measure in this chart is proportional to ds/sqrt(1-s^4). The measure fraction of |s|<eta is

integral_0^eta (1-s^4)^(-1/2) ds / integral_0^1 (1-s^4)^(-1/2) ds
<= eta/sqrt(1-eta^4).

For eta=1/10 this is less than 0.101. The closure of any arithmetic progression of multiples of P in the two real circles is a coset of a compact subgroup whose projection to either circle is surjective: any nonzero multiple of P remains a nontorsion real point. Haar measure therefore gives the union of the two bad sets measure less than 0.202. There is a nonempty open set where both |s_sigma|>1/10. Finite quotient poles and forbidden multiplication/translation values can also be avoided: each such condition has measure zero in the relevant surjective circle projection. This is the same real-progression principle already used in completeness, with a quantitative open condition added.

The selected H then satisfies |Norm(uH)|>1/(100sqrt(7)). Since R is in 2E and its two real abscissas are at least d_sigma,

|Norm(uR)| <= 1/sqrt(7),
|Norm(uR/uH)| < 100.

Also 0<fH_sigma<1, so for r>=10,

0<N<=(1+1/r)^2,
0<W<=(1+1/r)^4+10000*r^(-125)<2.

Finally

0<b=a*W^2/(1+a)^2<4/a<17.

All conditions of the source's preparation-zero completeness lemma (Brox v3 lines 2572-2599) now hold. Its inherited simultaneous two-twist argument provides the pole witnesses. The normalized denominator 1+a is automatically nonzero, and no new local correction choice is needed.


### Compatibility with the root-square-root Kummer entry

If the scalar entry reconstructs a point with abscissa belonging to S-P or S+P, all scalar contact divisibility and anchor inequalities apply to its actual nonzero integer label c_signed=±a-1, not silently to a-1. Its absolute value c satisfies ||a|-c|<=1. This is the only relation needed in the later height comparison; completeness chooses the original orientation S-P. The real bound above only uses R in2E, so it holds for either reconstructed orientation.


<a id="real-guards"></a>

## Real-part root guards and simultaneous real choice

This argument applies to the final direct-target source. It assumes the inherited prime-pattern theorem, local scalar preparation and real-group facts identified below. It proves compatibility of the four guards with the real scalar region; it does not prove pole completeness, the height theorem or global source arithmetic.

### Exact source and notation

Use the final direct-target normalization

\[
 K=\mathbf Q(\sqrt2),\qquad d=3-\sqrt2,\qquad D=d^2,
 \qquad E:y^2=x^3-Dx,
\]

\[
 P=\left((57-28\sqrt2)/8,\;(-660+417\sqrt2)/32\right).
\]

The fixed roots are \(Q_i=[n_i]P\), with all four \(n_i\ne0\). Completeness chooses

\[
 H=[h]P,\qquad U_i=[n_i]H,\qquad
 V_i=[n_i](H-P),\qquad U_i-V_i=Q_i.
\]

The final builder does not use the older \(h-4\) convention. Its fixed translation is \(P\). The two real embeddings are denoted by \(\sigma=+,-\), with \(d_\pm=3\mp\sqrt2>1\) and \(d_+d_-=7\). For \(a+b\sqrt2\), write \(\operatorname{Re}(a+b\sqrt2)=a\); this is the rational coefficient, equal to half the sum of the two real embeddings, not one chosen real embedding.

Source passages (paths relative to this package):

- `construction/318/build_source.cjs:427–444`: the four actual inverse guards on coefficient zero of \(f(V_i)-f(U_i)\).
- `construction/318/build_source.cjs:362–370`: the fixed curve and point constants.
- `docs/sources/quartic_v10.tex:19381–19415`: fixed point, infinite order, doubling, and real abscissa facts.
- `docs/sources/quartic_v10.tex:19580–19598`: nonzero root labels and final \(h,h-1\) convention.
- `docs/sources/quartic_v10.tex:19661–19678`: direct-target CRT and formal depth construction.
- `docs/sources/quartic_v10.tex:10632–10692`: real-progression lemma.
- `docs/sources/diophantine_optimization_20261106_v3.tex:3249–3302`: explicit component-group divisibility before prime selection. This passage uses the earlier \(h-4\) normalization; import its component-group argument, not its old CRT residues.

### Proposition: the four guard loci can be avoided

Let \(E_\sigma(\mathbf R)^0\) be the real identity component and let

\[
 G=\overline{\mathbf Z(P_+,P_-)}
 \subset E_+(\mathbf R)^0\times E_-(\mathbf R)^0.
\]

Then its identity component \(G^0\) is a connected compact real-analytic torus. Each projection of \(G^0\) onto its real elliptic identity circle is surjective. To see this, the projected cyclic orbit is infinite because \(P\) has infinite order. If the connected projection were trivial, the image of \(G\), which has finitely many components, would be finite. A nontrivial connected closed subgroup of a circle is the whole circle.

The fixed point lies in each identity component because it is a double. More generally, the real identity component is the unbounded oval consisting of \(O\) and the points with \(x\ge d_\sigma\). On this oval the rational function

\[
 f_\sigma=1/x
\]

has no pole, extends real-analytically at \(O\) with value zero, and is positive everywhere else. Analyticity at \(O\) also follows from the formal parameter expansion \(x=z^{-2}(1+O(z))\).

For each fixed nonzero root label define on \(G^0\)

\[
 g_i(H_+,H_-)=\frac12\sum_{\sigma=\pm}
 \left(f_\sigma([n_i]H_\sigma-[n_i]P_\sigma)
       -f_\sigma([n_i]H_\sigma)\right).
\]

This is globally real-analytic: multiplication, translation, and \(f_\sigma\) are real-analytic on the relevant compact circles. At the identity,

\[
 g_i(O,O)=\frac12\left(f_+(-[n_i]P_+)+f_-(-[n_i]P_-)\right)>0.
\]

Here neither \([n_i]P_\sigma\) is \(O\), since \(P\) has infinite order and the real embedding is injective on algebraic points. Thus \(g_i\) is not identically zero. A nonzero real-analytic function on a connected real-analytic manifold has a zero set with empty interior and measure zero. Each of the four loci \(g_i=0\) therefore has Haar measure zero in \(G^0\).

It follows that their union can be removed from any nonempty open scalar region without exhausting that region. The argument works in either possible dimension of \(G^0\) and does not assume independence of the two elliptic logarithms.

**Trace-zero distinction.** These are trace-zero loci, involving both real factors. They are not automatically inverse images of finite subsets under one projection. The older finite-pole argument alone does not establish their avoidance. The positivity computation at \((O,O)\) establishes nontriviality of each analytic guard.

### Quantitative scalar region

Define, on each identity circle,

\[
 s_\sigma=\sqrt{d_\sigma f_\sigma(H)},\qquad 0\le s_\sigma\le1.
\]

This nonnegative expression is sufficient for the measure computation; no globally single-valued signed square root on the circle is asserted. Along each of the two arcs, substitute \(x=d_\sigma/s^2\) into the invariant differential to obtain

\[
 \left|\frac{dx}{2y}\right|
 =\frac{ds}{\sqrt{d_\sigma}\sqrt{1-s^4}}.
\]

Consequently the normalized Haar measure of \(s_\sigma\le\eta\) is

\[
 \frac{\int_0^\eta(1-s^4)^{-1/2}\,ds}
      {\int_0^1(1-s^4)^{-1/2}\,ds}
 \le\frac{\eta}{\sqrt{1-\eta^4}}.
\]

The inequality uses that the integrand is increasing and that the denominator is at least 1. A surjective continuous homomorphism sends normalized Haar measure to normalized Haar measure. Thus the union bound applies on \(G^0\), without requiring independence of the two projections. With \(\eta=1/10\),

\[
 \Omega=\{H\in G^0:s_+(H)>1/10,\ s_-(H)>1/10\}
\]

is open and has measure at least

\[
 1-\frac{2}{10\sqrt{1-10^{-4}}}>0.79998.
\]

For the rational completeness charts \(f_H=u_H^2\), this gives

\[
 |\operatorname{Norm}(u_H)|>\frac1{100\sqrt7}.
\]

For any scalar point \(R\in2E(K)\), its two real abscissas are at least \(d_\sigma\), so

\[
 |\operatorname{Norm}(u_R)|\le\frac1{\sqrt7},\qquad
 |\operatorname{Norm}(u_R/u_H)|<100.
\]

The final builder has

\[
 q=\operatorname{Norm}(u_R/u_H)r^{-15},\qquad
 N=\operatorname{Norm}(1+f_H/r),\qquad W=N^2+rq^2.
\]

Indeed, `scalar.normalizedNormRatio` is `scalar.normUR * r^(-16)` divided by `scalar.normUH/r`. Since \(0<f_{H,\sigma}<1\), for \(r\ge10\)

\[
 0<W\le(1+1/r)^4+10^4r^{-29}
 \le1.4641+10^{-25}<2.
\]

For integral input \(\beta=3723(2X+1)^2\ge3723\), the displayed product

\[
 r=(\beta-1)(\beta-2401)(32\beta+343)(2\beta-1)
\]

is positive and exceeds 10. With \(a=114444r\),

\[
 0<b=a\left(\frac W{1+a}\right)^2<\frac4a<17.
\]

The earlier scalar-preparation derivation uses a different stage and exponent. The final source uses exponent −29; its exact consumers are `construction/318/build_source.cjs:820–844`.

### Compact uniform bounds and order of choices

Fix the four roots and their labels before applying the contact-prime theorem. Inside \(\Omega\), remove both the four zero sets above and the finite union of inherited quotient/pole loci. The latter loci are covered by the existing rational-function/pole argument; their relevant multiplications have nonzero labels.

The remainder contains a nonempty open set. Choose a nonempty open neighborhood with compact closure \(K_0\) lying in the remainder. Then

\[
 \epsilon=\min_{1\le i\le4}\min_{H\in K_0}|g_i(H)|>0.
\]

All four new guard inverses are uniformly bounded by \(\epsilon^{-1}\), and the finitely many other comparison functions are bounded on the same compact set. These bounds are fixed before the contact primes and the progression moduli arising from their reduction orders. No universal numerical lower bound on \(\epsilon\) is needed: the existing prime-pattern application permits an arbitrarily large real parameter after these bounds are fixed.

### Component divisibility and final CRT

Let \(m=|G/G^0|\). When choosing the prepared shared index and continuity modulus, require

\[
 64m\mid h_0,\qquad64m\mid L.
\]

This may be imposed before prime selection. The original local preparation permits additional fixed divisibility, and enlarging the continuity modulus preserves the local neighborhoods. The component-group argument is already explicitly present in Brox v3 lines 3249–3302.

For the final direct-target construction write

\[
 M_\pm=\operatorname{lcm}_p(d_\pm(p)/4),\qquad\Pi=\prod_p p.
\]

Use the inherited prime-pattern conclusions

\[
 \gcd(M_-,M_+)=1,\quad\gcd(M_-,L)=16,
 \quad\gcd(M_+,L)=1,
 \quad\gcd(\Pi,M_+)=\gcd(\Pi,L)=1.
\]

Then, for the primary-depth exponent \(e\) used in that construction,

\[
 h\equiv0\pmod{\Pi^eM_-},\qquad
 h\equiv1\pmod{M_+},\qquad
 h\equiv h_0\pmod L
\]

are compatible, since the only common divisor with the first and third moduli is 16 and \(16\mid h_0\). Enlarging the fixed \(L\) by \(m\) before prime selection is allowed: its odd factors enter the avoidance modulus, and the prescribed 2-parts remain controlled. This is an application of the stated prime theorem, not a new proof of it.

Every index in the resulting progression is divisible by \(m\), and its step is divisible by \(m\). If a progression is \(r+k\mathbf Z\), its closure in \(G\) is \([r]P+[k]G\). Since multiplication by a nonzero integer is surjective on the torus \(G^0\), and \(m\) annihilates \(G/G^0\), we have \([k]G=G^0\) whenever \(m\mid k\). Also \([r]P\in G^0\) when \(m\mid r\). Its closure is therefore exactly \(G^0\). The positive tail is dense in that closure by compactness/recurrence, so arbitrarily large positive indices meet the interior of \(K_0\).

This establishes simultaneous real scalar smallness, the four new guards, the inherited pole avoidance, and all prescribed local congruences. Chart signs at finite places are supplied separately by the existing reciprocal-branch construction; the new guards depend only on \(f=u^2\), so they impose no extra sign requirement.

### Soundness of the inverse guard

If \(f(V_i)-f(U_i)=a+b\sqrt2\), the rational inverse equation forces \(a\ne0\). Then \(a^2-2b^2\ne0\), since otherwise 2 would be a rational square. Thus the two rational field-quotient equations have a nonzero determinant and determine the quotient uniquely. This implication is already formalized as `ConcreteQuadraticDomains.norm_nonzero_of_real_nonzero`, at `proof/components/ConcreteQuadraticDomains.lean:54–60`.

For reciprocal charts the numerator used by the builder is \(u_Uv_V+u_Vv_U\), with denominator \(u_V^2-u_U^2\). The elliptic addition identity gives

\[
 \left(\frac{u_Uv_V+u_Vv_U}{u_V^2-u_U^2}\right)^2=x(U_i-V_i).
\]

The ordinary finite case follows by substitution in the secant formula. If one point is \(O\), use \(u=0,v=\pm1\) to obtain the same identity directly. Equal-abscissa cases have zero denominator and are excluded by the guard. The present completeness proof shows that excluding them, and even excluding the stronger trace-zero locus, loses no required integer-input witnesses.


<a id="six-helper-8-29-trivial-height"></a>

## Six-helper order 8/29 weights, including the new zero branch

For each detector retain delta=t−1, e, q1=e/delta³ on the nondegenerate branch, and the already needed eDelta=e*delta. Replace the seven old helpers by six coordinates a,b,c,x,A,y with quadratic rows

    a=e², b=a², c*delta=b²,
    x*eDelta=c², q1*A=x², q1*y=A².

For e*delta!=0 these uniquely give

    a=e², b=e⁴, c=e⁸/delta,
    x=e¹⁵/delta³=q8,
    A=e²⁹/delta³=q15,
    y=e⁵⁷/delta³=q29.

The eDelta assignment is moved earlier and reused, not duplicated. No previously computed evaluator power is assumed. This is six helpers in the actual norm-chain interface, one fewer than the prior seven.

### Why deleting the e inverse is allowed

It is NOT valid simply to assert e remains nonzero. The new equations permit additional zero-weight branches.

For a nonbase detector the retained equation is F(t)*e=(A_scale*delta)^5, and the audited height scale A_scale is nonzero. Thus e=0 implies delta=0 and t=1. Conversely delta=0 implies e=0 because F(1)!=0. The common-mu representation has A_scale*delta=mu*(t²−t), with mu*t=A_scale and mu!=0, so the same argument applies.

For the base detector the fused equations are q1*F(t)=delta² and e=q1*delta³. If e=0 and delta!=0, the second equation gives q1=0 and the first gives delta²=0, a contradiction. Thus this case also has t=1.

Whenever t=1, its logarithmic height is0. In the final three-detector height argument choose the effective contact radical for this detector to be1. Its height bound is immediate and every local divisibility obligation is vacuous. No claim about its arbitrary weight, trace or pole witnesses is needed. The downstream height transfer depends only on those two facts. The transformed five-contact parameter is3 in this exceptional branch, but even its specific radical need not be invoked because h(t)=0 directly.

On every remaining branch e and delta are nonzero, q1 is nonzero, and the six weight equations recover the intended values exactly. The previous W=0 empty-contact branch is handled as before. All old completeness witnesses use the nondegenerate branch and extend uniquely through the new six-helper formulas.

### Quotient domains

The potentially zero-denominator relations c*delta=b², x*eDelta=c², q1*A=x² and q1*y=A² must be represented as free existential witnesses with structural quadratic equations, not as globally uniquely defined quotients. The same applies to each detector's B relation and to nonbase q1 after deleting the e inverse. The F(t) denominator remains globally nonzero: if F(t)=0, the nonbase equation forces delta=0, contradicting F(1)!=0; the fused base equation gives the same contradiction. These metadata changes do not alter the coordinate or residual count.

<a id="square-root-kummer-scalar"></a>

## Square-root Kummer scalar translation for the V10 branch

### Scalar translation

This is a local algebraic replacement for the scalar point R=S−P. It permits the two abscissas x(S−P) and x(S+P), and consequently requires the explicitly stated, independently reviewed adjustment to the scalar height argument below. The two curve identities are formalized in `proof/components/ScalarJacobi.lean`.

### Equations

Write E: y²=x³−Dx over K=Q(sqrt(2)). The fixed point P has square chart P=(k²,km), with k and m nonzero and m²=k⁴−D. The root S has x(S)=h², where h is already present from the reversed reciprocal-root construction. The actual ordinate of S need not be assigned.

Introduce two field quantities r and g, giving four rational coordinates, with

- g=hr;
- g²−k²r²−2mg−k²h²−D=0.

Both field equations have degree at most two in the displayed rational coordinates. There is no x(S) assignment and no inverse of x(S)−x(P).

Set lambda=(g−m)/k. The second relation is exactly

lambda²=k²+h²+r².

Define jS=h lambda−kr and jR=hk−lambda r. Then the complete Jacobi identities give

- jS²=h⁴−D;
- jR²=r⁴−D;
- (h²−k²)lambda=h jS+k m;
- lambda(h²−r²)−h jS=r jR.

Thus S'=(h²,h jS) and R'=(r²,r jR) are elliptic points satisfying R'=S'−P. Since S' and the actual root S have the same abscissa, S'=S or S'=−S. Hence x(R') is x(S−P) or x(S+P).

The identities include the tangent case h²=k². There is no spurious infinity branch: r=0 would imply −k²h²−D=0, impossible in either real embedding because k²,h²,D are positive. The square chart similarly excludes nontrivial 2-torsion because ±sqrt(D) is not a square in K. The point R' is finite and nonidentity.

Assign nR=Norm(r), and define NUR by nR*NUR=1. These are two additional rational coordinates. Therefore the entire scalar translation plus half-norm entry uses six coordinates, with no S.x, S.j, R.y, or difference inverse. NUR is exactly Norm(1/r), the reciprocal square-root norm required by the existing half-norm scalar module.

### Converse and source completeness

For the source completeness witnesses, choose S'=S and R'=S−P. Both belong to 2E(K), so compatible square-root charts exist. The standard square-root difference formula gives r; putting g=hr satisfies the equations. Thus every required original completeness witness remains available.

### Scalar height and anchor adjustment

If S=[a]P with a odd, the reconstructed scalar point is [a−1]P or [−a−1]P. Its absolute label is c=|a−1| or |a+1|. In both cases c is even and

||a|−c|≤1.

These are the only label comparisons used by the V10 scalar height bound. The local scalar norm argument supplies the same order-32 divisibility of this reconstructed scalar label. The semilocal anchor applies to the same point R', with either sign of its square-root norm allowed. The existing 2-adic integrality needed for the affine parity packing continues to hold for every such R'. Completeness continues to choose the original minus branch.

### Interaction with root-product heights

Once all four root ordinates are absent from consumers, form Kprod as the product of their existing square roots h_i. Then C=Kprod² is the product of their abscissas. Neither the four root x assignments nor the field C assignment need be materialized. Geometry's norm-product scale and parity formulas apply directly to Norm(Kprod) and the product of its two rational components. Actual compiled savings must be measured because the compiler can already eliminate some assignment coordinates.

<a id="square-root-product-height-scales"></a>

## Shifted square-root product height scales

### Proposed scales and shared parity coordinate

Let the four nonidentity root points Q_i lie in 2E(K), K=Q(sqrt(2)), with abscissas x_i=h_i². Set Kprod=product(h_i)=k0+k1 sqrt(2), n=Norm(Kprod), and B=k0+n. Use the three rational scales

1, B², n².

Only the norm n needs a rational quadratic assignment after computing Kprod. Both remaining scales are squares of affine expressions. This removes the separate k0*k1 helper required to reconstruct the square of the trace of C=product(x_i)=Kprod². The affine parity anchor uses the same n via 2^12 n.

### Uniform positivity

At each real embedding, a nonidentity point in 2E(K) has x_i>d_sigma, where d=3−sqrt(2) and d_sigma>1. Consequently

|Kprod_sigma|>d_sigma²>2,
|n|>Norm(d)²=49.

Writing the two real values as a,b gives

|k0|≤(|a|+|b|)/2<|ab|/2=|n|/2.

Therefore |B|=|k0+n|>|n|/2>24.5, and both B² and n² exceed one. This preserves the positivity argument used to omit the detector W0 inverse guards when 0<mu<1. The unshifted scale k0² does not have this uniform lower bound and should not be used for that purpose.

### Height transfer with the existing constant

Suppose the unchanged detector argument gives h(lambda), h(B² lambda), h(n² lambda)≤T, where T=(H+log3)|N|^(19/k). Then h(B),h(n)≤T.

The polynomial of Kprod has coefficient vector [1,−2k0,n]=[1,−2B+2n,n]. Its projective height is at most

h([1,B,n])+log4≤h(B)+h(n)+log4.

This follows place by place: at finite places the integer linear transformation does not increase the local maximum; at infinity its row-sum bound is at most four. The standard Mahler-measure bound by the Euclidean coefficient norm now gives

2h(Kprod)≤h(B)+h(n)+log4+(1/2)log3≤2T+log4+(1/2)log3.

Since C=Kprod², its height is exactly 2h(Kprod). For H≥1 and |N|≥1,

2T+log4+(1/2)log3 < 7H |N|^(19/k).

Indeed, 2+2log3+log4+(1/2)log3<7. Once the parity anchor has forced all four root labels to be odd, the existing exact product-height identity h(C)=sum_i h(x_i) applies. The source bound B_label²−6<7H|N|^(19/k) is therefore unchanged.

### Parity and completeness

At the unique place above 2, v(h_i)=−3/2−v2(n_i). Taking norms gives v2(n)=−12−2 sum_i v2(n_i), so 2^12 n is 2-integral exactly when all root labels are odd. Once they are odd, it is a 3-unit. Thus the previously audited affine semilocal parity packing works unchanged.

The three scales are fixed positive nonzero rational squares once the roots are chosen, so they satisfy the same completeness requirements as the original scales. No stronger prime-pattern assumption is introduced. This is a local height/circuit refinement, not an independent proof of the inherited global arithmetic inputs. Actual coordinate savings require compiler measurement.

<a id="cusp-coordinate-estimates"></a>

## Cusp-coordinate estimates used in the final height argument

Let Gamma contain-I, have levelN and degree d, with genus g>=2. At a cusp of width1<=m<=N, use the actual uniformizer q_c=exp(2*pi*i*tau/m), so the base Tate parameter isq=q_c^m. The hyperbolic region Im(tau)>3 embeds as a punctured cusp disc, completed atq_c=0.

Primary context: Javanpeykar arXiv1403.6404, sections2.3 and 3.5, and the standard modular j-function expansion. The elementary bounds below are supplied explicitly rather than attributed to a new theorem in those sources.

### 2. A non-Weierstrass point in these discs

Use the Belyi map pi_X=1728/j, of degree d, and set M=2^128. Consider a_i=1/(M+i), for 1<=i<=g^3+1. There are at most g^3-g Weierstrass points. Since these fibers are disjoint, some fiber contains a non-Weierstrass point b. All its complex conjugates have the same rational j-value 1728(M+i). Every Galois conjugate of the canonical congruence cover is again a congruence cover of the same degree and level at most N: on the full-level modular model, Galois acts through the cyclotomic determinant on the components and conjugates the level subgroup inside GL2(Z/NZ). Thus Bruin's bound applies uniformly to every conjugate. In the actual application the pinned source already uses the rational modular model X_H and its rational j-map, so its conjugates are this same cover. This modular-model fact is essential; the common rational j-value alone would not justify uniform analytic bounds.

Every such lift, after reduction by SL2(Z), has Im(tau)>10. Here is an elementary coarse justification. On the standard fundamental domain, |q|<1/100. The formula

    j(q)=q^(-1) E4(q)^3 product_(n>=1)(1-q^n)^(-24)

and sigma_3(n)<=n^4 give |E4(q)|<4 and the product factor<2, hence |j(q)|<128/|q|. If Im(tau)<=10, this is at most128 exp(20*pi)<2^135, whereas1728(M+i)>2^138. The coarse numerical inequalities can be replaced by direct rational bounds if desired.

The height of a_i satisfies

    h_naive(a_i) <= 100 + 3 log(g+1).

For |q|<=exp(-20*pi), the same product formula, or Cauchy's estimate applied to G(q)=qj(q), yields

    |d(1728/j)/dq| >=128,  and  |q|^(-1)<=2|j|.

For clarity, G is analytic on |q|<=1/100 and bounded by 128. On |q|<=1/200, |G'|<=25600. At |q|<=exp(-20*pi), this implies |G-1|<1/4 and |G-qG'|>1/2; substituting in1728(G-qG')/G^2 proves the displayed derivative bound.

Since q=q_c^m, it follows that

    -log |d pi_X/dq_c| <= log |q|^(-1) <= h_naive(a_i)+9.

### 3. Wronskian bound in the same coordinate

Take the outer q_c-circle corresponding to Im(tau)=3, whose radius is R_c=exp(-6*pi/m). Our b has |q_c(b)|<=exp(-20*pi/m). A Euclidean disc centered at b of radius

    rho=(R_c-exp(-20*pi/m))/2

lies in the embedded cusp chart and satisfies

    rho >= exp(-21)/m >= exp(-21)/N.

Indeed1-exp(-14*pi/m)>=(1-exp(-14*pi))/m by concavity. This is the only shrinking-coordinate-radius cost, and it is logarithmic in N.

Let omega_j=f_j(q_c)dq_c be an orthonormal basis. Its L2 integral on this embedded disc is at most1. The power-series integral on the disc gives

    |f_j^(k)(b)/k!| <= sqrt((k+1)/pi) rho^(-k-1).

Hadamard's inequality applied to the Wronskian determinant therefore gives the generous bound

    log |Wr_(q_c)(b)| <=100 g^2 log(2gN).

This also covers the convention with unnormalized rather than factorial-normalized derivatives. The final height proof uses this coefficient estimate directly. Its Arakelov metric contribution cancels against the point-height contribution, as shown in [the derivation](#height-49-over-8).

<a id="direct-divisor-finite-bound"></a>

## Direct finite-place bound without the modular-degree factor

### Setting

Let pi:Y->X=P^1_(O_L) be the normalization finite cover in Javanpeykar Theorem4.3.2, and psi:Y'->Y its minimal resolution. Let f=pi*psi. The resolution is semistable and regular. Let K_Y' be the divisor of the rational relative differential d(pi), as in his section 4.2. Let D_hor=[0]+[1]+[infinity]. For each rational vertical branch prime p put m_p=floor(log d/log p), where d=deg(pi). Define the effective Cartier divisor on X

D_bound = D_hor + 2 sum_p m_p*div_X(p).

The sum can be restricted to p|6N for Gamma_H by the separate modular-vertical-support lemma. Here div_X(p) includes the ramification multiplicities of primes of O_L overp.

At every nonexceptional prime divisor of Y', local different bounds imply

K_Y' <= f^*D_bound

coefficientwise. Horizontally the different is e-1<=e, and the relative canonical base divisor K_X=-2[infinity] only reduces the coefficient. Vertically Javanpeykar Lemma4.2.3 gives r<=2e*m_p*e_p, exactly the coefficient of the displayed pullback. Outside the branch support the coefficient is zero. No estimate on a pushed-forward branch divisor is used.

### Extending the inequality across exceptional curves

This step avoids assuming that the ramification divisor on the possibly singular normalization is Cartier.

Set Z=f^*D_bound-K_Y', a Cartier divisor on the regular resolution. It is effective away from the exceptional curves. For each exceptional irreducible curve E,

(Z,E)=-(K_Y',E)<=0,

since f^*D_bound has intersection zero with a contracted curve and minimality plus adjunction gives (K_Y',E)>=0. This is exactly the minimal-resolution input used in Javanpeykar Lemma4.2.1.

Suppose Z had a nonzero negative part. It is supported on exceptional curves. Write Z=Z_+-N with Z_+,N effective and having no common components, and N nonzero exceptional. For every E in the support ofN,

(N,E)>=(Z_+,E)>=0.

The final inequality uses positivity of intersection of distinct effective curves on the regular arithmetic surface. Therefore(N,N)>=0. This contradicts negative definiteness of the exceptional intersection matrix. Hence N=0 and Z is effective everywhere.

This is a direct negativity proof. It requires neither an unproved Cartier property of K_Y nor a numerical-pullback formalism on the singular normalization.

### Intersect the chosen section

Let P':Spec O_L->Y' be the closure of a rational point b above the rational valuea, with a outside0,1,infinity. Its image is not contained in the effective difference. The preceding divisor inequality and the projection formula for the pullback of D_bound give

(K_Y',P')_fin/[L:Q]
 <= (D_hor,Q)_fin/[L:Q] + 2 sum_p m_p*logp
 <= 3h(a)+2 sum_p floor(logd/logp)*logp.

For the modular cover the sum is at most omega(6N)*logd. Thus the finite contribution is

3h(a)+2omega(6N)logd,

with no factor d. The factor d in the previously used bound came from pushing R to pi_*R and then bounding its intersection with the entire base section. That is unnecessary for this direct divisor domination.

### Verification obligations and scope

The argument needs the ordinary local-different coefficient interpretation of d(pi) away from the exceptional locus, the published local bound in Javanpeykar Lemma4.2.3, minimality/adjunction for exceptional components, and negative definiteness. These are all inputs already used in his section 4.2. It does not assert a new upper bound for every arithmetic metric or a final contact exponent. Archimedean differential and Wronskian contributions remain to be combined separately.

<a id="finite-exceptional-primes"></a>

## Finite exceptional-prime refinement for the 318-coordinate source

### Proposed fixed set

Let

    S_bad = {2,3,5,7,11,13,17,37,41,73,109,359,439,2399,4801}.

Every listed number is prime. Their product is

    B_bad = 11185621387570686764517810 < 2^84.

Define M5(a) using exactly the inherited five contacts infinity, 0, 1, 2401, -343/32, but omit only S_bad. The associated detector radicals use the five positions 0,-1/2,-1,1/2399,-32/407, again omitting S_bad.

This change does not change any polynomial row. It is a stronger soundness argument about more primes. Completeness can retain its old choice of primes greater than 76176 and every old local congruence; no stronger prime-pattern theorem is needed.

### Consumers of exceptional primes

1. **Five-contact geometry and height theorem.** The inherited moduli argument is smooth outside210, and every determinant of the primitive five contact forms has support in{2,3,5,7}. The exact same ramification statement therefore holds with R=B_bad*M5(a): rad(D_L*N_bad) divides R. See quartic_v10.tex lines6915--7001. None of the modular-support, direct-finite-divisor, metric-cancellation or fixed-dimensional isogeny arguments needs a lower bound76176 on the primes of R. They use only its prime support and size. Thus the reviewed49/8 theorem applies with this new B_bad.

2. **Detector contact map and its delta denominator.** The five positions together with 1 have all numerator, denominator and pairwise-difference support in{2,3,5,7,11,37,109,439,2399}. This is also the exact list printed in the inherited height-transfer proof (lines11108--11117). Outside that list, consumed contacts have delta=t-1 a unit and exactly one odd factor. The map phi(t)=2+1/t has determinant-1. The degenerate t=1 branch has phi(1)=3 and every contact prime lies in this same set, so its new radical is still1.

3. **Elliptic model, fixed translation and orientation.** K/Q is unramified away2. D=(3-sqrt2)^2 has norm49, so good unramified local computations require only2,7. The fixed P has x=(57-28sqrt2)/8 and y=(-660+417sqrt2)/32. The numerator norms factor as41^2 and 2*3^2*7*17*41. Hence x(P),y(P) are units at both places outside{2,3,7,17,41}. This covers the Norm(V0) orientation contradiction and the exceptional H=P branch. The h(P),j(P) constants have numerator norms -2*41 and -3^2*7*17, adding no primes. Other group identities are characteristic-zero identities and use no prime cutoff.

4. **Pole soundness.** The exact original and preparation-zero pole lemmas exclude negative odd valuations at every prime outside{2,3,17}, not merely above76176. Normalized pole equivalence introduces no prime restriction. The norm-chain parity argument needs only odd residue characteristic, unramifiedness and D a unit. The new affine delta=v-1 leaves have even valuation for every such prime, as proved in [the derivation](#parity-even-linear-delta-leaves).

5. **Scalar input and contact collisions.** beta=3723(2X+1)^2, with 3723=3*17*73. Outside{2,3,17,73}, any nonzero valuation of beta is even, so the omitted beta=0 and infinity contacts cannot be odd. The four retained factors are(beta-1),(beta-2401),(32beta+343),(2beta-1). All pairwise collision and denominator primes of 0,1,2401,-343/32,1/2 lie in{2,3,5,7,359,4801}; specifically718=2*359 and 4801=2*2401-1. At a consumed contact the relevant r valuation is positive odd and the other factors are units. The correction11 and normalizer114444=11*(2*3*17)^2 add only{2,3,11,17}. Global nonvanishing of r, W and 1+114444*r is the independent rational squareclass/Q2 argument, unchanged by this inventory. beta=0 continues to use h(beta)=0 directly.

6. **Actual rational logarithms and precision.** The high Padé(2,1) coefficient denominators have prime support{3,5,13}; the low J1 has denominator5. At a formal point their quotient denominators are units outside those primes. Their exact errors begin in degree 4. The full formal series has coefficients binom(2j,j)/(4^j*(4j+1)) in reciprocal u, and the rational z-series differs by the square-root factor with coefficients integral away2. The required relative precision 16 and the weak primary-log unit estimate hold for p>17 by the sharper coefficient argument below. Every prime outside S_bad is at least19. Global Padé denominator/numerator nonvanishing is already proved over K and imposes no further local exclusions.

7. **Anchor and real completeness.** The fixed anchor is tested only at 2,3; its half-norm and parity proof is unchanged. Real selection and preparation-zero completeness are unchanged. The selected Gaussian primes can still be chosen above76176, so their reduction-order, ray and quartic-reciprocity lemmas need no extension to small primes.

### Independently verified tail estimate

For H_j=binom(2j,j)/(4^j*(4j+1)), at an odd prime p one has v_p(H_j)>=-v_p(4j+1). If p>17, then for every j>=4,

    4j - v_p(4j+1) >= 16.

For j=4 this follows because p does not divide17; for j>=5 it follows from v_p(4j+1)<=4j-16 (indeed logarithmic growth is much smaller). Hence at v(u)>=1, each omitted term relative to u has valuation at least16*v(u); valuations tend to infinity. The expansion in delta=v-1 has v(delta)=4v(u) on the forced positive branch, and the exact rational change of variables has denominators only2. The analogous G series is obtained by multiplying by the binomial square-root series, integral away2. Thus the same order 16 estimate applies. The complete change-of-series and actual quotient-denominator check is written in [the derivation](#small-prime-log-tail).

### Resulting proof and anchor constants

The reviewed contact theorem becomes

    h(a) < 2^68*C^2*(B_bad*M5(a))^(49/8)+128,
    C=210^300<2^2400.

The logarithm of the coefficient before+128 is below

    68+4800+(49/8)*84 = 5382.5.

Adding128 raises this by less than 1. The integer proof constant

    H_small = 2^5385

is therefore safe. It is a proof constant, not a new circuit coordinate.

The half-norm anchor S=3^(2^17) gives nonzero scalar label

    c in 2*3^(2^16-1) Z,
    log2(c)>98303.5.

Since log2(80H_small)<5392, one has9*5392=48528<98303.5 and(15/64)*98303.5>5392. Thus the same high13, low4, scalar-index 8 contradictions hold with very large margins. In fact S=3^(2^16) gives log2(c)>49151.5>48528 and(15/64)*49151.5>5392, so it also suffices. S with exponent 15 does not satisfy this particular high-relation estimate and is not claimed.

A frozen fixed-constant successor could therefore use S=3^(2^16), as realized and independently replayed in the final reduced-anchor318/decimal326 pair. This changes no symbolic coordinate count, and is expected to shorten the ordinary constant chain by 7 relative to exponent 23. The earlier exponent 23 checkpoint remains preserved; the final accepted pair uses the literal exponent 16 parameter. No later conductor proposal is incorporated.

<a id="height-49-over-8"></a>

## Contact-height exponent 49/8 by metric cancellation

### 1. Inputs and coordinates

Use the same Q-defined modular cover X_H -> X(1), genus g>=2, degree d, level N, and pi=1728/j as in the preceding height13 and 37/4 notes. All conjugate complex covers have the same level and degree; in the actual application the cover and map are Q-defined. Choose a non-Weierstrass b above one of a_i=1/(2^128+i), 1<=i<=g^3+1. There are at most g^3-g geometric Weierstrass points, so one fiber avoids them. Every complex lift has imaginary part above10 in a cusp coordinate q_c=exp(2*pi*i*tau/m_c), with width m_c<=N.

The explicit elementary j-expansion and embedded-disc estimates in [the derivation](#cusp-coordinate-estimates) give

- h(a_i)<=100+3log(g+1);
- -log|d pi/dq_c|(b_sigma)<=h(a_i)+9;
- an embedded Euclidean q_c-disc centered at b_sigma of radius rho>=exp(-21)/N.

No Arakelov Green-function estimate is needed below. The local coordinate may vary with sigma; the two metric occurrences use exactly the same q_c at that embedding.

### 2. Direct finite-place domination

Use docs/arithmetic.md#direct-divisor-finite-bound. On the semistable minimal resolution Y' of the normalization of P1_O_L in X_H, let K_Y'=div(d pi). The modular vertical-support lemma restricts branch primes to p|6N. Set m_p=floor(logd/logp) and

    D_bound=[0]+[1]+[infinity]+2 sum_(p|6N) m_p div(p).

At nonexceptional prime divisors, Javanpeykar Lemma4.2.3 gives the exact coefficientwise inequality K_Y'<=f^*D_bound. The horizontal inequality follows from e-1<=e; the -2[infinity] base canonical divisor only helps. Vertically, the coefficient is at most2e*m_p*e_p, precisely the coefficient of the displayed pullback.

For Z=f^*D_bound-K_Y', minimality and adjunction give Z.E=-K_Y'.E<=0 at each exceptional curve. If the negative part N_Z were nonzero, it would be exceptional and N_Z.E>=Z_+.E>=0 on its components, contradicting negative definiteness. Thus Z is effective. Intersecting the chosen section, whose generic point lies outside the branch support, gives

    F_b:=(K_Y',b)_fin/[L:Q]
      <=3h(a_i)+2 sum_(p|6N) floor(logd/logp)logp
      <=3h(a_i)+2omega(6N)logd.

The point-height inequality is the minimal-model inequality in Javanpeykar Lemma2.3.1; we do not assert equality of the stable minimal height and the chosen-resolution height.

### 3. Exact metric cancellation

Let k=g(g+1)/2. Javanpeykar Theorem2.4.1 states

    h_F(J_H)<=k*h(b)+log||Wr||_Ar(b).

His definition of h(b) and the displayed decomposition in the proof of Theorem4.5.1 give

    h(b)<=F_b - avg_sigma log||d pi||_Ar(b_sigma).

At each embedding, write d pi=(d pi/dq_c)dq_c and Wr=Wr_q*(dq_c)^k. Then

    log||d pi||_Ar=log|d pi/dq_c|+log||dq_c||_Ar,
    log||Wr||_Ar=log|Wr_q|+k log||dq_c||_Ar.

Consequently the metric terms cancel exactly, preserving the inequality:

    h_F(J_H)<=k F_b
       -k avg_sigma log|d pi/dq_c|(b_sigma)
       +avg_sigma log|Wr_q|(b_sigma).

There is no remaining Bruin metric bound, cusp-width-linear metric term, or Green-function normalization constant. This is a different way to combine the two published quantities, not a claim that each quantity separately has a stronger bound.

### 4. Wronskian coefficient bound

For an L2-normalized holomorphic differential omega=f(q_c)dq_c, its integral on the embedded disc is at most1. Orthogonality of power series on the disc gives

    |f^(j)(b)/j!|<=sqrt((j+1)/pi)*rho^(-j-1).

Applying Hadamard to the g by g matrix of derivatives gives the previously verified generous estimate

    log|Wr_q|(b)<=100g^2 log(2gN).

This estimate uses only the local Euclidean disc and the global L2 normalization, not an estimate on the Arakelov cotangent metric.

Put L=log(6dN). Since g<=d, omega(6N)<=log(6N)/log2, h(a_i)<=100+3log(g+1), and L>=log6, the preceding bounds give, with ample slack,

    h_GR(J_H)<=2^11*d^2*L^2.                        (1)

Normalization: Javanpeykar Lemma2.4.4 states that the Gaudron-Rémond height is h_GR=h_Fal+g log(sqrt(pi)). The preceding cancellation bounds h_Fal. Add g log(sqrt(pi))<g before using Rémond and Gaudron-Rémond below. The displayed2^11 bound has ample slack to absorb this, so(1) and all later h_F notation use the GR/Rémond normalization.

For example F_b+h(a_i)+9<=409+12log(g+1)+2log(6N)logd/log2, and the Wronskian term is at most100d^2L. All these terms are below the right side of(1).

### 5. Explicit contact exponent

Retain N<=C R^2, C=210^300 and R=B_* M5(a). The elementary index estimate may be sharpened to

    d,g<2^14 C R^(97/32).

Indeed (1+1/p)^32<=p for p>=13, and the remaining product over 2,3,5,7,11 is1152/385<3. This is the same index argument as the independently checked73/24 estimate, with the indicated elementary Euler-product exponent. Since3*4608<2^14, the prefactor is unchanged.

Now L<4096+6logR<2^13 R^(1/32), using logR<12R^(1/32). Inserting this and the index bound in(1) gives

    h_F(J_H)<2^65 C^2 R^(49/8),

because 2*(97/32)+2*(1/32)=49/8.

The actual image C_A of the source's nonzero A->J_H map has dimension2. Rémond Corollary1.2 and the existing Bost lower bound imply

    h_F(C_A)<=h_F(J_H)+3g/2<2^66 C^2 R^(49/8).

Apply Gaudron-Rémond Theorem1.9(1) directly in dimension2, with no polarization hypothesis, over L', [L':Q]<=2304R. The half-log isogeny variation is

    8*(32log14+logd'+log max(1,logd',h_F(C_A))),

which is smaller than 2^17 R^(49/8). Hence

    h_F(A)<2^67 C^2 R^(49/8),
    h(a)<2^68 C^2 R^(49/8)+128.

The inherited CM bound854R is smaller. The old constant H19=2^110 C^6 B_*^19+128 therefore remains valid for

    h(a)<=H19*M5(a)^(49/8).                         (2)

### 6. Adopted source consequence

Use low order 4, high order 13, norm-H order 4. The primary z/full-log relative precision is16. A Pade(2,1) approximation gives alternate relative precision 16 with only one field quotient helper; its numerator is quadratic and denominator affine. Low J1 already has precision 8.

The conditional five-helper weight chain is

    a=e^2,
    c*delta=a^2,
    q4*(e*delta)=c^2,
    q1*q7=q4^2,
    q1*q13=q7^2.

Thus c=e^4/delta, q4=e^7/delta^3, q7=e^13/delta^3 and q13=e^25/delta^3 on the ordinary branch. The existing t=1 exceptional-height branch handles e=0, exactly as in the frozen 332/335 sources. The quotient outputs must remain free structural witnesses, not falsely documented globally nonzero quotient gates.

The high contradiction exponent is2-4*(49/8)/13=3/26. The old 3^(2^25) anchor gives c>(80H)^12 and therefore more than the required power9. The low exponent is2-(49/8)/4=15/32. The adopted scalar uses order 15 with ri^16, preserving index 8: the full norm-ratio valuation is at least30, one local valuation is at least15 and is even after formality, so it is at least16. Then h(beta)<=H*c^(49/64), and c^(15/64)>80H follows easily from log2(c)>25,165,823.5 and log2(H)<2,093,966. The old W<2 real-completeness estimate replaces r^-61 by r^-29, still harmless for r>=10.

These mathematical consequences are used by the frozen 318-coordinate construction. A counting correction is essential: the three variable J logarithms must retain their delta-squared helpers for the branch membership tests, so replacing their Padé(3,2) approximants by Padé(2,1) does not remove those coordinates. Only V0 loses its unshared input-square helper, saving two rational coordinates. Together with three saved weight helpers and one scalar-power helper, this stage measured332->326. The subsequent parity-even linear delta refinement removed eight more coordinates, giving318. The accepted smaller fixed-anchor and ordinary-lift proofs are separate notes; the ordinary companion has326 variables.

### Padé(2,1) domains

The G approximant is (1-61w/65+16w^2/195)/(1-7w/13), and the J approximant is (1+12delta/65-2delta^2/195)/(1+5delta/13). Their exact errors start at degree 4. The G denominator root13/7 is not a square inK=Q(sqrt2), while the actual w=D*f^2 is a K-square. The J denominator rootdelta=-13/5 would give v=-8/5, impossible for the real reciprocal curve v^2=1-D*u^4. The numerator discriminants7003/12675 and 952/12675 are neither rational squares nor twice rational squares, so neither numerator has a K-root. These are actual-domain denominator proofs; unlike the earlier Padé(3,2) denominators, these linear denominators do have roots inK at arguments excluded by the source. At the formal place both denominators are units, since their constant terms are1 and all coefficient denominator primes are below the good-prime cutoff.

### Verification boundary and primary references

Primary sources used here:

- Ariyan Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, with an appendix by Peter Bruin, arXiv:1403.6404. The relevant inputs are section 2.3, Theorem2.4.1, Lemma2.4.4, section 4.2 and Theorem4.3.2. https://arxiv.org/abs/1403.6404
- Gaël Rémond, *Propriétés de la hauteur de Faltings*, Annali della Scuola Normale Superiore di Pisa23(2022),1589–1596, Corollary1.2 and the stable-height observation on page2. https://www-fourier.univ-grenoble-alpes.fr/~remond/2476.pdf
- Éric Gaudron and Gaël Rémond, *Degrés minimaux d'isogénies et invariants des variétés abéliennes*, Theorem1.9(1) and section 1.5, current author version. https://lmbp.uca.fr/~gaudron/art20.pdf

The final source uses S = 3^(2^16) and H = 2^5385; see [exceptional-prime bounds](#finite-exceptional-primes).

<a id="modular-vertical-support"></a>

## Vertical branch support for the Gamma_H cover

Let N be the modular level, H a subgroup of (Z/NZ)^* containing -1, and X_H=X_1(N)/H. The source uses H=ker(epsilon) for a weight-two nebentypus, so epsilon(-1)=1. Let pi=1728/j. The normalization of P^1 in the function field of X_H is finite etale away from the horizontal sections 0,1,infinity and the vertical primes dividing 6N. The statement persists after any number-field extension used in the semistable-model construction.

### Direct proof on the open j-line

Put U=Spec Z[1/(6N),j,1/(j(j-1728))]. Over U consider

E_j: y^2=x^3-3j/(j-1728)*x-2j/(j-1728).

Writing a=-3j/(j-1728), b=-2j/(j-1728), we have
4a^3+27b^2=-108*1728*j^2/(j-1728)^3.
Thus the discriminant is a unit and the j-invariant is j. This is an elliptic scheme over U.

Multiplication by N is finite locally free and has invertible differential N, hence is finite etale. Therefore E_j[N] is finite etale over U. Its locus T of points of exact order N is open and closed: this can be checked after an etale trivialization E_j[N]=(Z/NZ)^2. In particular T is finite etale.

H acts on T by multiplication. The action is free on geometric points, since a primitive point P satisfies hP=P only when h=1 modulo N. More directly, under the equivalence between finite etale covers and finite locally constant sets, the quotient T/H is again a finite locally constant set. It is consequently represented by a finite etale U-scheme. This argument does not require |H| to be invertible on U; taking invariants of an arbitrary ramified cover would not justify the same assertion.

We identify its characteristic-zero generic fiber with the coarse Gamma_H moduli cover. Away from j=0,1728 every elliptic curve with a given j is etale-locally isomorphic to E_j, and its automorphism group is {+1,-1}. Two choices of isomorphism differ by this group. Since -1 belongs to H, the induced H-orbit of a primitive point is independent of the isomorphism. Thus the finite etale sheaf T/H is exactly the coarse sheaf of elliptic curves with a primitive N-torsion point modulo H. On the generic fiber this is Y_1(N)/H, equivalently the open part of X_H. No choice of a quadratic twist remains in the quotient.

U is regular and therefore normal. A finite etale U-scheme is normal. The just-identified cover is consequently the normalization of U in the generic function field of X_H. This proves the claim about the open part of the normalization of P^1. The coordinate change pi=1728/j is an isomorphism on the indicated open after inverting 6, taking j=infinity,1728,0 to pi=0,1,infinity.

After replacing Z by a number ring O_L, the etale model remains etale by base change and remains normal because the new base open is regular. It is therefore still the relevant normalization. At every prime of O_L not over 6N, the generic point of the vertical fiber belongs to this open, so there is no vertical branch component there. Resolving the normalization in Javanpeykar's construction does not change the branch locus of its finite normalization map; the resolution is handled separately by his inequality.

### Exact effect in Javanpeykar's finite-place bound

In the proof of Proposition 4.2.4 (printed pp.24-25), before the final coarse estimate, the wild vertical contribution divided by [L:Q] is bounded by

2d * sum_{p with vertical branch} floor(log d/log p)*log p.

For the modular cover, restrict the sum to p|6N. Each summand is at most log d, giving 2d*omega(6N)*log d. The horizontal part is d*(0+1+infinity,Q)_fin/[L:Q] <= 3d*h(a), not 3d^2*h(a). For the positive-genus modular curves here, d >= [SL2(Z):Gamma0(N)] >= N and d>=3, so every p|6N is <=d and contributes to the same vertical group in that proof. We may therefore use the sharper finite contribution

3d*h(a) + 2d*omega(6N)*log d.

If a separate low-degree exceptional modular curve is ever used, it should be treated directly rather than silently using d>=3.

### Sources and verification scope

- Javanpeykar, Polynomial bounds for Arakelov invariants of Belyi curves, Proposition 4.2.4 and its proof, and the proof of Theorem 4.5.1. The displayed prime sum is explicit in the proof; the restriction to 6N is the new modular input proved above.
- Cais and Conrad, Modular curves and Ramanujan's continued fraction, section 2 and Theorem 2.2, pp.3-4: https://math.arizona.edu/~cais/Papers/Preprints/J5.pdf . It gives the standard integral full-level models and cites Katz-Mazur 10.9.1 and 10.9.6-7. Our open-cover proof avoids needing a claim about a quotient compactification being smooth.
- Katz and Mazur, Arithmetic Moduli of Elliptic Curves: https://doi.org/10.1515/9781400881710 . Standard moduli interpretation of level structures and their integral models.
- Stacks Project, finite etale covers and their finite-set description: https://stacks.math.columbia.edu/tag/0BL6 . Multiplication by N on abelian varieties: https://stacks.math.columbia.edu/tag/0BFG and https://stacks.math.columbia.edu/tag/0BFH . The relative elliptic-scheme assertion follows fiberwise finite flatness and the invertible differential, or the usual abelian-scheme multiplication theorem.

This note establishes support of vertical branching and the uncoarsened finite contribution. It does not by itself prove a final exponent, an explicit Faltings-height constant, the fixed-dimensional isogeny transfer, or a new Diophantine source.

<a id="small-prime-log-tail"></a>

## Formal-log and Padé accuracy outside primes at most17

Let p>17 and work at an unramified place of K=Q(sqrt2), normalized by v(p)=1. Assume D is a unit. All reciprocal points considered here satisfy v^2=1-Du^4, and on the forced positive branch put w=Du^4 and delta=v-1. If r=v(u)>=1, then v(w)=v(delta)=4r.

### 1. A sharper denominator bound for the full series

The direct reciprocal integral is

    H(w)=sum_(j>=0) h_j w^j,
    h_j=binom(2j,j)/(4^j(4j+1)).

Thus v(h_j)>=-floor(log_p(4j+1)). The direct-parameter logarithm is -u H(w). On the positive branch, the old z-parameter series is

    G(w)=sqrt(1-w)*H(w),
    z=-u/v,
    log_E=z G(w).

The equality follows either by differentiating or by the exact equation
4w(1-w)G'+(1+w)G=1-w, with constant term1. The coefficients of sqrt(1-w) lie inZ[1/2]. Therefore the coefficient g_j ofG satisfies the same bound

    v(g_j)>=-floor(log_p(4j+1)).

Likewise the full direct delta-series is J(delta)=H(-2delta-delta^2). Its jth coefficient is an integral linear combination of h_n with n<=j, so it satisfies the same bound. This bound is substantially sharper than the factorial bound used for the old cutoff76176.

### 2. The whole infinite tail

For j=4, 4j+1=17<p, so the coefficient is integral. For every j>=5,

    floor(log_p(4j+1))<=j-4.

Indeed19^(j-3)>4j+1 atj=5, and induction preserves the inequality. Consequently forr>=1,

    4jr-floor(log_p(4j+1))>=16r

for everyj>=4, and these lower bounds tend to infinity. Thus the entire tail beginning at degree 4 in eitherG(w) orJ(delta) has valuation at least16r. The tail beginning at degree 2 inJ has valuation at least8r. Every nonconstant term ofG has valuation at least4r, so the primary approximation byz has relative precision 4r.

The unramified good-reduction formal logarithm is an isometry on v(z)>=1 forp>2. Sincev(z)=v(u)=r on the formal branch, the preceding estimates are relative precision bounds for the point logarithm, not only coefficient estimates.

### 3. Padé(2,1) approximants

Use

    P_G=1-61w/65+16w^2/195,   Q_G=1-7w/13,
    P_J=1+12delta/65-2delta^2/195, Q_J=1+5delta/13.

Both exact series differences Q_G G-P_G and Q_J J-P_J begin at degree 4. Their rational coefficients through degree 3 have denominators supported on{3,5,13}. Atp>17 all these coefficients are integral. Sincew anddelta have positive valuation, Q_G andQ_J are units. The previous tail estimate therefore proves relative accuracy16r for both Padé approximants.

Their leading error coefficients are-112/14365 forG-P_G/Q_G and 2/2873 forJ-P_J/Q_J, respectively; no use of those leading coefficients being units is needed. Extra numerator primes 47,149 from the global irreducibility discriminant are not local bad primes: the numerator is1 modulo the formal maximal ideal.

The low direct approximation J1=1-delta/5 retains relative precision 8r. Norm-H order 4 gives primary z-depth 4 and hence relative precision 16, sufficient for the high order 13 comparisons. Scalar-index order 8 uses only formal-log isometry and good reduction, not a higher truncation.

### 4. Actual-domain denominator and zero statements

The G denominator root13/7 is not a square inK, whereas actualw=Df^2 is a K-square. The J denominator rootdelta=-13/5 would forcev=-8/5, impossible at a real embedding ofv^2=1-Du^4. The numerator discriminants7003/12675 and 952/12675 are neither rational-square nor twice rational-square, so neither numerator has a K-root. These are global domain statements and do not add their numerator prime factors to the finite exceptional set.

Conclusion: all local formal-log, Padé accuracy and nonvanishing consumers in the current4/13,index 8 source are valid at every good unramified primep>17. No additional prime beyond{2,3,5,7,11,13,17} is required by this log module. The complete source still has other exceptional primes from its input, contact forms, fixed point and scalar product, which must be audited separately.

<a id="kato-scope"></a>

## Kato applicability and the remaining global dependency

The primary source is K. Kato, *Euler systems, Iwasawa theory, and Selmer groups*, Kodai Mathematical Journal 22 (1999), 313–372, [published PDF](https://www.jstage.jst.go.jp/article/kodaimath1978/22/3/22_3_313/_pdf), DOI [10.2996/kmj/1138044090](https://doi.org/10.2996/kmj/1138044090). The inspected PDF has SHA-256 `483dc18c56b2fe9cfac4e37f2e6594399625c3f0ea98a05bb69116377c67fc06`.

Theorem 0.8 and Example 0.6.2, printed pages 317–318, allow the coefficient prime 2 in the rational case localized at a DVR prime not containing 2. The stronger residual-irreducibility and integral-cokernel hypotheses concern primes containing the coefficient prime and are not the case used here. Lemma 12.7, page 364, accounts for the extra factor 2 at the small dyadic levels; that factor is invertible at the localization in question.

The consuming passage is the [pinned Version 10 manuscript](sources/quartic_v10.tex), lines 12610–12720. Its representation comes from E_l: y²=x(x−l)(x+3l), for the fixed positive squarefree l≡11 mod 12, not the different CM curve used to encode integer labels. Its j-invariant is 35152/9, hence nonintegral and non-CM. Serre's open-image input gives rational irreducibility and an open SL₂ subgroup in the image of the abelian-kernel Galois group. A quadratic character is trivial on that group; the same open subgroup therefore survives twisting. A nonidentity upper unipotent has a one-dimensional fixed space, verifying the stronger abelian-kernel condition. Complex conjugation has one-dimensional eigenspaces. The roots of Kato's arithmetic-Frobenius polynomial P_q(T) have absolute value q^−1/2, so condition 0.6(iii) has w=−1. The Tate-module Euler factor 1−a_q T+qT² becomes 1−(a_q/q)σ_q^−1+(1/q)σ_q^−2 under Kato's substitution, with the expected quadratic-twist factor on a_q.

The theorem controls H²₀, the kernel of local restriction, and the coordinate ideal of the actual retained nontorsion Euler-system class. It does not directly control all of H². Version 10 separately compares the j_* complex and full open-scheme cochains and pays the odd-place cone lengths with unused good-prime Euler factors and fixed old-place correction factors (lines 12693–12828). Verifying applicability still presupposes the manuscript's construction, norm relations and nonvanishing of that retained class. This source check is not a reconstruction of every cohomological step.

The support-uniform integral assertion 2^c_E u^ev∈Z₂[[t]][G] uses a different positive-complex argument, lines 12832–13075, followed by central calibration, lines 13078–13240. Kato's away-from-two theorem does not prove that integral assertion or the restricted converse. Compatible finite free models and determinant bases, uniformity in G and added conductor support, the completed-localization comparison, the calibrated determinant and subsequent coefficient/limit arguments remain consequential dependencies. Constants may depend on the fixed E_l; the asserted uniformity is not over all l.

The prior positive-complex and central-calibration arguments are present in the manuscript. Their complete independent validation, and the downstream chain through restricted converse, simultaneous descent, pole completeness and actual final-source witness assembly, are not established by this source check. This is an unresolved validation boundary, not a claim that those historical arguments are absent or disproved.
