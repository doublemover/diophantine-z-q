# A marked x112 shell at 19 gives a nonzero projected summand

For the bounded control \(D=-311,\ f=241,\ n=241\cdot311\), this computation takes **one** prescribed oriented shell, one literal post-\(T_7\) calibrated flag, and no sweep of moving arcs. It makes the actual 241 path and finds the complete contribution \(-28\equiv11\bmod13\) to the named \(M_5\) projected exponent. It is a single summand: the full local exponent at 19 and its class after summing the other arcs are unknown. This is not arithmetic on the original detector.

## 1. A physical Hecke flag and the actual quaternion lift

At the named place over 29 take the positive \(\mathcal H_7\) seed \(P=(81,614)\). The exact auxiliary flag \(Q=(184,556)\) is obtained by replacing \(Y\) with \(-Y\) on the calibrated characteristic-zero flag \((184,314)\). The verifier computes
\(\mathcal H_7(P,Q)=0\) **in characteristic zero**, and checks both endpoint class equations of discriminant \(-320\) for \(Q\) in the exact radical field. Thus it realizes an actual horizontal degree-seven edge of the selected fixed support; the ordinary finite coincidence alone is not the proof. This is the post-arrow \(Q\) instance, not a count of arbitrary degree-seven prepath kernels.

At 19 use \(s^2=2\), \(\sqrt D=5s,\ \sqrt{241}=4s,\ \sqrt{-n}=2\), and fixed coefficient roots \(\sqrt5=9,\sqrt6=5,\sqrt{-5}=8s\). The actual reduction of \(Q\) has encoded coordinates \((100,39)\) and \(j=7\). Use the verified maximal geometric order in the \(j=7\) model \(y^2=x^3-x+5\), basis \((\nu,\eta,\pi,\eta\pi)\), from the pinned inert-19 seed certificate. Write \(\tau=2\eta-1\); the pure quaternion coordinates \((R,C,D_0)/14\) are taken on \((\tau,\pi,\tau\pi)\), with norm \((7R^2+19C^2+133D_0^2)/196\). On the tangent \(d\tau=5s\).

The full marked flag is read by the actual 16-parameter both before and after its cyclic-three quotient. Test the auxiliary \(\beta=4\sqrt{-5}\) using norm 80, the named Lie action, exact maximal-order integrality at 2, and both ordered cyclic lines. In particular at the cyclic 16-line the scalar of \(\beta\) is either 0 or 8 because both source and target have 2-conductor 4: in the basic order modulo 16 the two stable same-conductor rays are \((0,1)\) and \((8,1)\), as in the previous exact fixed-calibration proof. The replay gives the unique \(\beta\) quaternion with these properties:
\[
  (\nu,\eta,\pi,\eta\pi)\text{ coefficients }(-22,22,16,13),
  \qquad (R,C,D_0)=(44,7,3).
\]
The actual cyclic 16 and 3 scalars are 8 and 1.

Use the exact target-order trace convention \(x=\operatorname{Trd}(W\beta)=112\) with \(\operatorname{Nrd} W=311f^2\). Eliminating one coordinate by the trace equation reduces each integer \(D_0\) to a quadratic with exact square-discriminant test. Test literal geometric integrality, the named tangent \(f\sqrt D\), and \((f+W)/2\) in the same order. For a pure quaternion, the coefficient vector in the displayed maximal order follows from
\[
2\nu=1+(5/7)\tau+2\pi+(4/7)\tau\pi,\quad
2\eta=1+\tau,\quad 2\eta\pi=\pi+\tau\pi .
\]
The exact unique retained \(W\) is
\[
      (-4081,4081,2431,1896),\qquad
      (R,C,D_0)=(8162,-9828,-3052).
\]
The actual order-two-adjusted endomorphism \((f+W)/2\) acts on the two marked groups by \(2f\bmod16\) and zero, giving the ordered moving marks \(2,0\) after dividing by \(f\). Testing \(W\)'s raw eigenvalues instead would not establish this.

## 2. A real 241 path and the completed moving lift

The reduction of \(W\) on 241-torsion is nonzero nilpotent, since \(W^2=f^2D\) and its integral order vector is not divisible by \(f\). Its image/kernel gives one actual cyclic \(f\)-path. For a compatible \(\mathbb Z_f\)-basis \((v,w)\) with \(v\) in that residue kernel, the source matrix of \(W\) has the shape
\[
 \begin{pmatrix}fa&b\\fc&-fa\end{pmatrix},\qquad b\text{ a unit}.
\]
The equality \(W^2=f^2D\) forces \(f\mid c\). On the enlarged target Tate lattice with basis \(v/f,w\), the endomorphism \(W/f\) is therefore integral. At primes different from \(f\), \(\alpha=(1+W/f)/2\) is integral by the previous test, and at \(f\) because \(2\) is a unit. This gives an actual maximal-order moving \(\alpha\) at the target. The induced full 16 and 3 marks are the ordered ones. Its dual line is nonhorizontal in the moving order since \(D\) is nonsquare at \(f\).

The finite quotient is computed by normalized Vélu and matched to the already verified \(D=-311\) canonical cycle at **vertex 18** (zero-indexed). Require equality of the transported \(\alpha\) with that vertex's actual map on two independent generators of full \(E[16]\) and two of full \(E[3]\), not merely stability on the marked lines. These torsion tests force equality of endomorphisms: the difference has degree at most \((2\sqrt{78})^2=312\), whereas the checked independent module has \(16^2 3^2=2304\) points. The only two matching scales give the same quotient up to sign. A direct Miller–Gauss computation on a source complement \(w\) with \(Ww\) gives the named negative sign. A separate calculation on the target's actual dual generator against its \(V=2\alpha-1\) image again gives \(\chi=-1\). Thus the coherent Weil sign is checked on both sides.

The auxiliary line is not horizontal at \(f\): if it were stable under \(\beta\) modulo \(f\), simultaneous triangular matrices and nilpotence of \(W\) would give \(x\equiv0\bmod f\), contrary to \(x=112\). So the auxiliary conductor of this 241-neighbor is \(4f\). The length-one norm defect is independently visible:
\[
 5(4f)^2\cdot311-(112/2)^2=1445052144,\qquad v_{19}=1.
\]
This depth is just the selected shell row; it does not assert the other depths on the full arc.

## 3. All factors of that one arc

Lift the **one** matched moving vertex's ordered 16/3 groups and actual dual-241 subgroup by the exact tame Hensel equations of the previous p19/p11 controls, and take the direct conductor-241 quotient. Both \(t_{16}\) views recover its actual marked curve-chart coordinates:
\[
 X=(14807603037,7844828191),\quad
 Y=(14128913153,12212020254)\pmod{19^8}
\]
in the basis \(1,s\). The residue is exactly \((100,39)\); no moving line was found by scanning.

At each of the four coefficient places ordered \((\sqrt5,\sqrt6)=(9,5),(9,-5),(-9,5),(-9,-5)\), all 160 factors have exact depth below the precision limit, and their largest depth is one. Their actual signed raw values of \(v_{19}(\mathcal U)\) are \(7,7,-7,-7\), respectively. The binary root of \(\sqrt{-5n}\) is \(9\cdot2=-1\bmod19\); its projected summand uses the sum of the first two values minus the last two, since the opposite moving root is inverted by complex conjugation. The relative residue degrees are one, and \(\chi=-1\), so the actual complete contribution is \(-28\equiv11\bmod13\). It verifies, for this one selected full lift, the independently frozen fixed depth-one prediction \(d_5(100,39)=28\). It is not a claim about the summed exponent at 19 or a unique way to cancel the 11 class.

Replay with Python 3 and python-flint 0.9.0 from the preserved donor-relative layout:

~~~sh
sha256sum -c SHA256SUMS
python3 -B check_x112_physical_mark.py | cmp - EXACT-D311-P19-X112-PHYSICAL-MARK.json
python3 -B check_x112_all_factor_depths.py | cmp - EXACT-D311-P19-X112-ALL-FACTORS.json
~~~
