# Exact supported k=0 admission cut on the original a=0 scalar

**Result.** On the original scalar at its own exact admissible \(h,J\), the only full \(\mathrm{Sel}_2\) class of the direct \(k=0\) Jacobian whose three coordinates are **positive** and supported on
\[
 \{5,11,17,163,661,733,1489,1861,131,6551\}
\]
is the identity. The first eight primes are precisely the actual \(\beta\); the last two occur in the actual \(\theta\). The last remaining nonzero tuple in this support is defeated by a **literal new numerator prime 88079**, without factoring the scalar's enormous numerator. This does not rule out classes with negative classes or outside support, a \(k=0\) rational point, other \(k\), or a full original PointPair.

## 1. Exact scalar bytes and same cover

Use the [materialized original scalar](../../joined-work-20261120/rc-linked-scalar-specialization-r1/ACTUAL-MATERIALIZED-SCALAR-SPECIALIZATION.md) with \(a=0\), \(h=473592745039516333133760\), and the single exact \(J\) transcribed into \(\texttt{PINNED-SCALAR-INDEX.json}\) from its frozen JSON. This is the original scalar at an admissible index; the three detector rows of a finished four-pole linked grid are **not** supplied. Its same label is \(s=1+6^{15}3^{65536}J\). Use \(R=4376874610839020\) and the scalar factor \(A_{\rm src}=114444R=17\cdot12^2\beta\), where
\[
 \beta=204618888056724185=5\cdot11\cdot17\cdot163\cdot661\cdot733\cdot1489\cdot1861.
\]
The literal scalar circuit is
\[
 H=\operatorname{Norm}U(h),\quad f=\operatorname{Re}(U(h)^2),\quad I=\operatorname{Norm} U(s-1),
 \qquad Q=I/(HR^{15}),\quad N=1+(H/R)^2+2f/R,\quad W=N^2+RQ^2 .
\]
Thus \(b=A_{\rm src}[W/(1+A_{\rm src})]^2\) and \(c=12 W/(1+A_{\rm src})\) gives \(\mu=b/17=\beta c^2\). No use of \(W=1\) globally, even when a finite source row proves that congruence.

Write \(c=a_c/D\) reduced, \(A=\beta a_c^2\), \(C=D^2-A\), and \(\delta=C/D^2\). The marked \(k=0\) Jacobian and class are the same as in the [literal contact Cassels derivation](../ct-original-k0-contact-cassels-r1/ACTUAL-CONTACT-CASSELS-REJECTION.md):
\[
 J:y^2=x(x-4A^2)(x-A(A+3D^2)),\qquad \Lambda=(1,C,C).
\]
Here only the shared curve and Kummer coordinates are imported, **not** the detector support/congruence hypotheses. The [source depth at 131](../../joined-work-20261120/rc-linked-scalar-genus-one-r1/ACTUAL-A0-THETA-131.md) and [literal scalar p² calculation at 6551](../../joined-work-20261120/rc-linked-scalar-specialization-r1/ACTUAL-THETA-MODULAR-ROWS.md) concern this same scalar and prove \(v_{131}(C)=v_{6551}(C)=1\). Their \(\delta/p\) units are 82 and 684, respectively; D is a unit since \(\mu\equiv1\) at each. They are the two used **proved** theta primes, not an assertion that no others occur. The source also has \(v_2(\mu)=4\) and \(\mu\in\mathbb Q_2^{\times2}\), and \(v_3(\mu)\ge2\) even, with D a unit at both.

## 2. Exact Kummer rows before the new moving place

Fix a positive squarefree tuple \((d_1,d_2,d_3)\) in the stated support, with their product a square. At each support theta prime the first coordinate of any point is square: the roots \(4A^2,A(A+3D^2)\) collide to the **nonzero square** residue \(4A^2\), and away from the collision the product of these two factors has square class one. The same statement follows by continuity at the exceptional torsion points or by their exceptional Kummer values. Thus \(d_1\) divides \(\beta\).

At any odd \(p\mid\beta\), valuation of A is odd, and \(C\equiv D^2\) is a unit square. In the three ordered coordinates the two rational torsion generators have classes
\[
 ([3A],[-1],[-3A]),\qquad (1,[-3A],[-3A]).
\]
Their parity vectors are \((1,0,1),(0,1,1)\), so they generate the whole local image of order four. In the first slot the exact condition on \(d_1\) is therefore \((d_1/p^{e_p}\mid p)=(3\beta/p\mid p)^{e_p}\), \(e_p=v_p(d_1)\), where divisions by p are integer divisions before reduction. The 256 exact squarefree possibilities leave \(d_1=1\) alone. In the second slot the first torsion exponent must then be zero, and the condition for \(d=d_2=d_3\) is \((d/p^{e_p}\mid p)=(-3\beta/p\mid p)^{e_p}\). On the ten-prime support the exact positive survivors are
\[
 1,\quad 3408665291,\quad 9291112901939,\quad 72485172522267769 .
\]

At 3 put \(m=v_3(A)\ge2\) even. The two nonzero root depths are \(2m,m+1\). A generic point with all three unit classes has even valuation of x. Below depth \(m+1\), all three factors have the same 3-adic squareclass, so are squares; above depth \(m+1\), the third factor has odd valuation. Equality is already excluded by odd valuation of x. Hence the only all-unit tuple at 3 is the identity; exceptional torsion classes are dealt with by continuity of the Kummer map. At 2 scale x and y by \(2^4,2^6\) to get roots of depths \(6,0\); the third root is an odd unit of class 3. If x is a square and has depth less than 4, its second factor has the same class. At depth 4 both other factors have unit class 5 (the second differs by the ratio \(1-4\,\text{odd}\)); at greater even depth the third again has unit class 5. The depth-4 choice x=16 in this scaled chart gives the actual nontrivial unit tuple \((1,5,5)\). Thus the relevant test for odd d is exactly \(d\equiv1,5\bmod8\) and \(d\equiv1\bmod3\). It leaves \(1\) and \(d_*=72485172522267769\). At the two known theta primes the singleton coordinate is 1 and the remaining coordinates allow the full local squareclass group: their paired unramified nonsquare line is present, and the Kummer class at \(4A^2\) gives odd depth because \(v_p(C)=1\). All unknown primes dividing C admit this tuple too: there d is a unit and the paired unramified line suffices. The issue is not the unknown theta factorization.

## 3. Literal moving numerator place 88079

Use the two roots \(7969,80110\) of 2 in \(\mathbb F_{88079}\). In each arm the literal curve is \(y^2=x^3-(3-\sqrt2)^2x\), with \(R_0=(1+\sqrt2,2\sqrt2)\). Reducing the very same two indices \(h,s-1\) uses two certified orders 3670 and 5505. Their order certificates check the displayed multiple is zero and all prime-denominator proper multiples are nonzero. Here the \(U\) chart is \(2y/(x^2+(3-\sqrt2)^2)\), regular at every used point, so all reductions and denominators are legitimate. The exact output is
\[
 U(h)=(16807,79510),\quad U(s-1)=(17819,19933),\quad
 (H,I,f)=(78061,51599,31925),\quad (N,Q,W)=(71812,13600,0).
\]
Both \(R\equiv49463\) and \(1+A_{\rm src}\equiv82401\bmod p\) and H are units. This proves **positive even** depth of the literal \(\mu\) there, even though no exact exponent of W beyond positivity is required. p divides neither \(\beta\) nor \(d_*\).

At this odd prime scale x by \(p^{v_p(A)}\) (a square) and y by its power \(3/2\). The zero and second roots collide, while the difference between their common residue and the singleton root has unit class \(-3\beta\). The exact finite symbols are \((-3\beta\mid88079)=+1\) and \((d_*\mid88079)=-1\). The singleton Kummer factor is consequently always a square: on the cluster this follows from the square residue, off the cluster from the other two factors' square product and the cubic equation. The candidate third coordinate \(d_*\) fails. This is a genuine actual local obstruction to that **second test class**, not to the original marked class \(\Lambda\), which is already everywhere local. In particular there is no Cassels rejection of \(k=0\) furnished by this ten-prime **positive** support.

The support limit is essential: c is given by the literal source circuit, not replaced by a small representation; neither all Selmer components nor global rational existence have been determined.

## Replay

    python3 -B verify_actual_scalar_88079.py | cmp - EXACT-ACTUAL-SCALAR-88079.json
    sha256sum -c SHA256SUMS

The final certificate uses only the single exact finite place and the at-most 1024 matrix subsets, not the preliminary bounded row scan. No Lean build, remote write, or claim of a finished grid.
