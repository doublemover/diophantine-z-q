# One compact j-map: all local coefficients, then degree and genus

The function field \(K\) is that of the same genuine \(X_1(M)_\mathbb C\),
and \(J\in K\) is the one forgetful modular coordinate used before.
The source does not manufacture the actual compact curve or its
analytification. In the final genus declaration the degree base field
is the literal \(\mathbb C(J)=\texttt{IntermediateField.adjoin }\mathbb C\{J\}\);
a separate reference function field cannot be passed as the degree.
For the number-field budget, degree of this same finite map survives
extension to \(\mathbb C\) (for the genuine geometrically integral
curve). A native bridge identifying the function fields of the base
change remains distinct; an auxiliary evaluation field does not
enter this degree or the isogeny theorem.

## Sharp native local seam

For each geometric closed point, supply the actual DVR \(B_P\) in
this fixed \(K\), a uniformizer \(z_P\), and the integral frame
\(dz_P\mapsto1\). This is the hypothesis of [Stacks 53.12.3](https://stacks.math.columbia.edu/tag/0C1B#lemma-curves-smooth-differentials-uniformizer).
Choose its actual branch tag. The finite probes are \(J\), \(J-1728\),
and \(J-a\) for ordinary \(a\); the cusp probe is \(J^{-1}\). The
analytic chart inputs are the genuine source and target germs of
that probe and their relation \(S=F(z^e)\) from the already computed
chart:
- Above \(0\), exact \(ST\) rotation and absence of source elliptic
  stabilizer give \(e=3\).
- Above \(1728\), exact \(S\) rotation and absence of source elliptic
  stabilizer give \(e=2\).
- At the cusp \(g\infty\), exact modular translation gives
  \(e=w=M/\gcd(M,c)\), read from the actual matrix \(g\).
- At every other point both stabilizers are trivial, so \(e=1\).

The base germ \(F\) has a simple zero; no order of any source germ is
assumed. The same native analytic-order check and named cusp theorem
derive that order. The actual comparison identifies analytic order of
\(S\) with the valuation of its specified algebraic probe, preserving
the true local parameter. The join inverts the cusp probe to recover
\(J\) with **negative** order, then uses the localized intrinsic
Kähler construction. It always differentiates \(J\), not the probe.
The strict anti-monotonicity of signed powers of \(\nu_P(z_P)\in(0,1)\)
identifies the unique actual integer coefficient of \(\operatorname{div}(dJ)\).
The `all_coefficients` theorem gives one proposition for **all**
geometric points of this one function, including the infinite ordinary
locus with coefficient zero. It assumes neither a different analytic
surface nor a finite enumeration of the ordinary locus.

## Sum on the genuine finite fibers

The canonical degree identity of this same curve (rank \(g\) of its
true Hodge basis) supplies \(2g-2\) as the sum of the actual
coefficients on the three finite fibers. Ordinary points contribute
zero by the preceding theorem. Complex residue degrees equal one;
over an unsplit number field they cannot be discarded. The additional
degree facts are the genuine finite-map ramification sums
\(\sum_{P\mapsto a}e_P=d\) for \(a=0,1728,\infty\).
Now `genus_of_same_map` derives \(3c_0=d\), \(2c_{1728}=d\) and
the canonical term \(2c_0+c_{1728}-d-c_\infty\); it calls the existing
same-map genus theorem. In particular \(2g-2<d\) for the same \(J=1\)
fiber, and the previously used rank ceiling remains
\(g\le M^2/24+1/2\). The ordinary inverse-disk and stable-lattice
witnesses retain precisely their prior hypotheses.

## Optional fixed-prime improvement

On paper the exact primitive count is
\(2d=M^2\prod_{p\mid M}(1-p^{-2})\) (prime-power count times CRT,
then **one** single sign quotient). The independent
`SelectedPrimitiveCRTRatio318` consumes this exact genuine product,
not a substitute degree, and checks \(13d<4M^2\) from the 15 mandatory
support factors. Its native scope is the rational product inequality
after the CRT identity, **not** a native proof of the general
prime-power/CRT cardinality formula. With the derived
\(12g\le d+6\), this gives \(g<M^2/39+1/2\).
