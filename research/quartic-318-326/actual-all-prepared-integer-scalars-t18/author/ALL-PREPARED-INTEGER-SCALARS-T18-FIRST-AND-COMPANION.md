# A fixed \(t_*=18\) first point for every prepared integer scalar

For each integer input and each already prepared literal scalar at its own native index, this gives its exact first point and one rank-free equivalent certificate for the second point. It fixes the point parameter in the native ABI, provides its ordered Kummer mark, and does not replace the complement by any other twist. It does not assert that simultaneous four-Ready indices or companion points have been obtained for every integer input.

## 1. The squarefree base depends on the input, not on the index

Fix \(a\in\mathbb Z\), actual shared labels and the native index \(h\). Assume the scalar \(b=\texttt{PreparedIntegerSource318.scalarB}\) is prepared and has its literal real range \(0<b<17\). Set \(B=17b\), \(R_a=\texttt{ScalarForwardWitness318.inputR}(a)\), \(L_a=114444R_a\). The integer casting and large-input lemmas give \(R_a\in\mathbb Z\), \(R_a>10\). The exact packed scalar value is
\[
 b=L_a\left(\frac{W}{1+L_a}\right)^2,\qquad
 17L_a=102^2\cdot187R_a,
\]
with its actual \(W\) at \(h\). Let \(\beta=\operatorname{sf}(17L_a)=\operatorname{sf}(187R_a)\) be the unique positive squarefree representative. If \(17L_a=\beta g^2\), \(g>0\) integral, then
\[
 \rho=g\frac{W}{1+L_a}>0,\qquad B=\beta\rho^2.
\]
Indeed \(W\) is a sum of squares with positive coefficient \(R_a\) and is nonzero because \(b>0\). Neither \(W\) nor \(h\) needs to be factored to define \(\beta\).

The native all-input lemma \(\texttt{ScalarSmallPrimePreparation318.actual\_multiplier\_values}\) gives \(v_2(L_a)=4,\ v_3(L_a)=2,\ v_{17}(L_a)=2\). In particular \(v_{17}(17L_a)=3\), so **every** such \(\beta\) contains 17 and is nonsquare; \(2,3\nmid\beta\). This is not an empirical observation at a few selected inputs. The scalar support-unit preparation gives a square reduced denominator for \(b\) and the exact same three scalar valuations \(v_2(b)=4,\ v_3(b)=2,\ v_{17}(b)=2\).

## 2. The real branch and the native first equation

Use the fixed first-point constant \(t_*=18\), not the detector contact parameter. Put
\[
 \mu=\beta t_*^2,\quad A=1+3\mu,\quad k=(1-\mu)(1-9\mu),\quad n=\beta k .
\]
Since \(\beta\ge17\), we have \(\mu>1\), \(k>0\) and \(A^2-k=16\mu>0\). On \(E_n:y^2=x(x-n)(x+3n)\) the exact first point is
\[
 (u,v_0)=\bigl(\beta A^2,\ 8\beta^2t_* A(1-3\mu)\bigr).
\]
The two identities
\[
 u-n=(4\beta t_*)^2,\qquad u+3n=4\beta(1-3\mu)^2
\]
give the equation and ordered class \(([\beta],1)\) in the \((x,x-n)\) slots. The first point and fixed base depend only on \(a\). Scaling abscissa and ordinate by \((\rho/A)^2,(\rho/A)^3\) gives the exact first abscissa \(B\) and the native parameter and ordinate
\[
      T=\frac{Bk}{A^2},\qquad
      y_1=\frac{8\beta^2 t_*\rho^3(1-3\mu)}{A^2}.
\]
Thus \(y_1^2=B(B-T)(B+3T)\), \(y_1\ne0\), \(0<T<B\), and the ordered class is \(([B],1)\) in the literal \((x,x-T)\) slots. In the native \(\texttt{PointPair.certificate}\) conversion the final scalar row parameter is \(e=T/b=17k/A^2\in(0,17)\). No change to \(b\), labels, \(h\), physical anchor or detector coefficient is made.

## 3. A single equivalent rank-free companion test

Set \(\delta=1-b/17=1-B/289\in(0,1)\). For this fixed \(T,y_1\), the original raw companion exists if and only if there is an affine rational point on
\[
             w^2=\beta(v^2-k\delta)(v^2+3k\delta).                 \tag{1}
\]
At a rational point of (1), \(v\ne0\): at \(v=0\) the right side is \(-3\beta (k\delta)^2<0\). The point \((\beta v^2,\beta v w)\) is on \(E_{n\delta}\). Scaling its coordinates by \((B\rho/A)^2,(B\rho/A)^3\) gives the **exact** second native data
\[
               s=\frac{Bv}{A},\qquad
               y_2=\left(\frac{B\rho}{A}\right)^3\beta v w .
\]
Indeed the new curve parameter is \(n\delta(B\rho/A)^2 = TB^2\delta\), and its new abscissa is \(B s^2\). The two first/second formulas are precisely \(\texttt{NormalizedPolePoints318.PointPair}\) at the same \(b\). Conversely, a PointPair at this fixed \(T,y_1\) gives \(v=As/B\ne0\) and \(w=y_2/((B\rho/A)^3\beta v)\); the second equation becomes (1). All displayed denominators, and the native certificate divisors \(b,s\), are nonzero. The ABI permits \(y_2=0\); no division by \(w\) or \(y_2\) is used. The four geometric branch roots of (1) are distinct and its two points at infinity are defined over \(\mathbb Q(\sqrt\beta)\), not rational. Thus asking for a point on its smooth completion is equivalent here.

**Square complement case.** If \(\delta=j^2\in\mathbb Q^{\times2}\), no rank or descent condition is needed: set
\[
                   v=jA,\qquad w=8\beta t_*(1-3\mu)j^2 .
\]
The two factors in (1) are \(j^2(A^2-k),j^2(A^2+3k)\), so this point is exact and yields a native companion with \(s=Bj\ne0\). No general claim of square \(\delta\) is made.

**Nonsquare complement case.** The same fixed-base secant presentation as at input zero works uniformly, with no trace-index or rank assumption. Set \(a_{\rm sec}=v_0/u\) and
\[
 F_-=(m-a_{\rm sec})^2-4u,\qquad
 F_+=(m+a_{\rm sec})^2+\frac{12n^2}{u}.
\]
The rank-free equation \(F_- F_+=\delta Z^2,\ Z\ne0\) is equivalent to (1). Indeed \(F_+>0\) over \(\mathbb R\). Put \(q=Z/F_+\ne0\), \(D=\delta q^2\) and \(r=((1-D)m-a_{\rm sec}(1+D))/2\). Completing the square in \(F_-=D F_+\), using \(a_{\rm sec}^2=u+2n-3n^2/u\), gives
\[
         r^2=\frac{(u-nD)(u+3nD)}{u}.
\]
With \(v=A/q,\ w=A r/q^2\) this is (1). Conversely, from (1) put \(q=A/v,\ D=\delta q^2,\ r=wq^2/A\), take \(m=(2r+a_{\rm sec}(1+D))/(1-D)\), and put \(Z=qF_+(m)\). The inverse denominator \(1-D\) is nonzero because \(\delta\) is nonsquare, and \(Z\ne0\). This exact correspondence does not require any Selmer dimension or use the input-zero one-bit trace calculation. The coefficients of the secant polynomial are fixed once \(a\) is fixed, whereas the right side contains the actual \(\delta\) for this \(h\).

## 4. Local admissions, but not a global construction

The stronger ordered class \(([\beta],1)\) on \(E_{n\delta}\) is admitted everywhere. At the real place and at \(2,3,17\), \(\delta\) is a local square by the preparation and \(\delta=1-B/289\). For instance the depths of \(B/289\) there are \(4,2,1\). At every other prime \(p\mid\beta\), \(v_p(B)\) is odd and cannot be negative because \(B=17b\) has square reduced denominator at \(p\); thus \(1-B/289\) is a square unit by Hensel. Wherever \(\delta\) is square, the known fixed first point transfers with its ordered class. Wherever \(\beta\) is square, the ordered class is the trivial one.

At a remaining prime \(p\ge5\) where \(\beta\) is a nonsquare unit, \(p\) does not divide \(k\): a residue root of \(1-\beta t_*^2\) or \(1-9\beta t_*^2\) would make \(\beta\) a residue square. Also \(v_p(\delta)\) is even. If \(B/289\) has positive valuation, \(\delta\) is a unit; if negative, its value equals that even valuation; if zero, its stripped unit is nonsquare and hence not 1. Thus \(n\delta\) becomes a unit after local square scaling. The curve with parameter a unit has good reduction and full rational 2-torsion at \(p\ge5\); its ordered Kummer image is the four unit pairs, since both slots have even valuation (including the specialized root values) and \(E(\mathbb Q_p)/2E(\mathbb Q_p)\) has size four by good reduction and the odd-residue formal kernel. It therefore contains \(([\beta],1)\). Scaling a point in an admitted local Kummer class and moving within its open local coset if necessary gives a representative away from \(x=0\) and the identity, and hence a local affine point of (1). This is an all-place proof, not a Hasse principle for the genus-one quartic.

In a simultaneous source argument the old existential preparation must still return the actual labels, anchor and one \(h\) with the three Ready detector poles and its scalar. The present identities consume any such scalar **at that very \(h\)**. Their one remaining scalar arithmetic input is (1) on the actual complement at that \(h\), unless its complement is already certified square. The other three raw PointPairs remain separate premises. No assertion of simultaneous preparation for every integer \(a\), computed class, global companion, rank or solution is made.

## Exact native bindings

All files are from the same original retained source.
- ScalarForwardWitness318.lean, 9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c.
- ScalarPolePreparation318.lean, 721851a467f0e8f34e4e6cb267aae94af3bf9da73e1c570d332c7f0b3c85ee10.
- ScalarSmallPrimePreparation318.lean, f698093eaa546054c69885cbd0e4bb5bb406fdf24f29a953aeba2693f5e38428.
- AllScalarSupportPreparation318.lean, db7793cdd7327ad737a3312dcda0962096a803ddca61caf8ba90d1657604c677.
- PreparedIntegerSource318.lean, e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423.
- NormalizedPolePoints318.lean, 410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542.

The two-input first-side arithmetic donor is checksum-list d89938215c030b787965c3761f79f3f1c5d23e8c94f10c17e0b15cb8b0e4b679 (only the preceding symbolic identities are needed here). No prime scan, global companion solver, or native build is used.
