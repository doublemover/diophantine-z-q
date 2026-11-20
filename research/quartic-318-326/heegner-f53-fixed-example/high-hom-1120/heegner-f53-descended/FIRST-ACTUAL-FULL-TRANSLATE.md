# A genuine signed conductor-323 summand, at a = 1

Same fixed level, curve, maximal CM order, β=60875, inert place and
tangent u as `../heegner-f53-oriented/LITERAL-F53-ORIENTED-PROJECTION.md`.
This goes beyond the mere level-48 projection but is not a high-level
point or a 20-class trace.

1. In F53^16 with w^16=2, u=8w^8, find a genuine marked 17-generator by
   the exact Ω−(1−r) projection. In F53^18 with w^9=25+12u, use the
   identical marked 19-generator procedure. The two fields are literal:
   X^16−2 is irreducible by the binomial criterion, and over k,
   X^9−(25+12u) is irreducible because its radicand has order 27 and
   gcd(9,(53²−1)/27)=1; w^9 already generates k. The larger fields are
   only arithmetic workspaces. The original C17/C19 subgroup schemes
   and their isogenies are k-defined, since Frob_k acts as [-53].
2. For odd l, let K(X) be the monic polynomial of the (l−1)/2
   distinct x-values of the genuine kernel. Put f=X³+AX+B,
   G=K'/K, d=(l−1)/2, t=sum kernel x-values. The normalized
   Vélu x-map is
   `R=X+4f(G²−K''/K)−2 f'G+2dX−2t`.
   Indeed each pair ±P with x(R)=r contributes
   4 f(r)/(X−r)² + 2 f'(r)/(X−r) by the point-sum definition of Vélu.
   The y-map is yR', from invariance of the differential. This portable
   k-morphism lets the 17-map act on the actual 19-generator, and both
   act on the marked 16 and 3 generators in their different fields.
   The script checks every nonzero geometric kernel point against
   direct Vélu and independent signed nonkernel values.
3. Form B=A/C_d by actual 17 and 19 quotients. Carry Ω to B by its
   genuine descent through the stable marked subgroup, without
   reconstructing any degree-l² primitive roots. Let φ:A→B be the
   normalized composite. Both degrees are coprime to #A(k)=54², so
   φ induces a bijection on actual k points. Use >228 distinct x-pairs
   `(x(φT),x(φΩT))`, all actual rational points in the same fixed
   modules. The degree-114 x-map is uniquely reconstructed by exact
   rational Euclidean interpolation; difference of competing rational
   expressions would have numerator degree at most 228. The
   differential is the nonzero (1+u)/2, so the y map is determined as
   `yR'/((1+u)/2)`. The polynomial identity for the target elliptic
   equation and disjoint signed samples check this over and above the
   argument from unique interpolation. The same trick works for
   repeated horizontal 29 transitions where transporting old E[29]
   on a killed eigenspace would not.
4. With this actual endomorphism, choose independent nonzero
   marked/opposite generators P_l,Q_l in B[l] for l=17,19.
   These are the same eigenlines as image C_{l²} and image A[l]
   by prime-to-p Tate module lattice descent (full generators of
   C_{17²}, C_{19²} are not needed). At this initial B choose the
   fixed Weil root from the chosen ordered P,Q pair. The a=1 line
   takes P_l+Q_l in each primary component. Push the very same 19
   line through the 17-map before quotienting, and push the original
   C16,C3 through all four actual isogenies. The code does not yet
   output Miller pairing values, nor does it independently
   normalize a different row to the same root.
5. The genuine compact order at the mixed target is read using
   `Ω_d=(1+dα)/2`, which descends because dα kills B[d], and
   dB ≡ 1 mod 96 checks the exact same level-48 orientation label.
   Both ordered raw low-level edge arrays and the canonical
   X0(48) chart are recomputed. The based φ0 value is:

       B = E(12+35u,43+16u)
       first mixed E(19+21u,17+7u)
       final mixed E(16+39u,50+5u)
       (t16(z), t16(3z)) = (38+29u,44+35u)
       (x48,y48) = (38+25u,11+42u)
       φ0 = (27+16u,25+u).
       χ_{-323}(1) = +1.

There are 288 unit branches in each class and 20 true class labels.
The actual next step is computing uniform prime Weil roots and
transporting them through all degree 29/5/7 arrows and the vertical
prime isogenies. It cannot be replaced by an arbitrary orientation
choice on every class. Grouping by stage, φ0 results can be cached on
ordered genuine transition labels. The exact independent signed stable
lattice labels serve as a checksum, not the evaluator.

## Independent direct t16 algebra (does not use j lookup)

Translate an actual order-2 kernel point R=(x0,0) to x=0. If
P4 is a prescribed order-4 generator, write
v=x(P4)−x0, a=3x0, b=3x0²+A, k=a/v, so v²=b.
Then `t4=64/(k−2)`: the normalized first/last t2 are
256/(k²−4), 1024(k+2)/(k−2)² by direct Vélu, and match the
two normalized rational degeneracies. This proves the function
identity on the actual moduli curve by generic uniqueness, including
its nonsingular specialization at exceptional j.

For order 8 and P4=[2]P8 let
s=(x(P8)+x(3P8)−2x0)/v, where R=[4]P8.
Adding R sends x−x0 to b/(x−x0), whence the displayed sum is
intrinsic to the unlabeled cyclic group. Doubling gives
`(s−2)²=4(k+2)`. Under the normalized quotient the corresponding
t4 values are 256/((s−6)(s+2)) and 256(s−2)/(s−6)²:
the shifted v'=(s−2)v and a'=(k+6)v. Thus
`t8=32/(s−6)` gives the correct ordered functions, even at
an ambiguous pair of t4 labels. For P16 compute t8 first and
last, denoted a8,b8; then
`t16=(b8−2a8)/(a8+4)` by the two true degeneracies.
The denominator is nonzero on noncuspidal level points, since
t8=−4 is a cusp (or the next forgetful t4 has a pole there).
The direct script checks exact agreement on the first two projections.
The top x48,y48 map still needs an extra ordered 3-level chart in
the rare case where its two projected t16 values do not suffice.

For such an extra chart the marked 3-Hauptmodul is also directly
available: P3=(x,y), m=(3x²+A)/(2y), m²=3x; put
K3=4m³/y, then t3=729/(K3−27). The tangent translation
to the actual flex produces Tate normal equation
Y²+2mXY+2yY=X³, proving the invariant and branch.
