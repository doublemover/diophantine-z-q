# The direct CM4 test needs only the one negative level-2544 coefficient

Keep the existing exact fixed real algebraic quaternionic lift F and its Jacquet–Langlands newform g of conductor 2544. Keep the actual reduction of F at the same prime over 13 onto the pinned order-13 function λ of the degree-two low map at all 416 marked labels. Keep the earlier short negative Sirolli–Tornaría source with auxiliary +37, and denote by A⁻₃₇(d) its **phase-normalized** coefficient at −d modulo 13. No positive coefficient or auxiliary CM field is used in the conclusion.

For squarefree positive d≡11 mod24 with (d/53)=−1, use the exact same direct CM4 construction with K=Q(√−d), including its prescribed cyclic 16, cyclic 3 and 53 residue orientations. Let Λ_d be the reduction of the ordinary full Hilbert point in the pinned 13-primary line at 53. Then
~~~
Λ_d² = 4 · A⁻₃₇(d)²  in F₁₃.
~~~
In particular one short negative unit per twist suffices; on a common selected q the two required coefficients are A⁻₃₇(Rq) and A⁻₃₇(Rθq), not four coefficients. Equality of squares suffices and does not predict a fixed unsquared phase across d. No production unit or actual numeric same-q pair follows.

## The characteristic-zero direct period, normalized before reduction

In the definite quaternion algebra of discriminant 53 let P₄(d;F) be the **unaveraged** sum of F over the literal oriented ring-class orbit of the direct construction. The local moduli orbit transport uses the same marked double coset as the finite calibration, including the fine conductor (4,4). For each d conjugate to a fixed embedding of its torus and right-translate F to F_d so this is the sum of F_d over Pic(O₄) in that frame. This translation is an isometry in the fixed Petersson norm, not a renormalization of the F values. In particular its direct finite reduction is
~~~
P₄(d;F) mod13 = 2 Λ_d.
~~~
The factor 2 is the independently verified exact Hilbert descent of the low mapped point; there is no division in the full reduced point group.

At 2 the torus K₂×/Q₂× is compact, represented by O_{K,2}× because K₂/Q₂ is unramified. Replace the transported F_d by its normalized right torus average \bar F_d at 2 only. Trivial central character makes this an ordinary orthogonal projection. The pointwise average is the literal mean over the six unit cosets O_{K,2}×/O_{4,2}×: the actual level-lattice stabilizer in the torus is exactly O_{4,2}×. All units of K are ±1; the kernel of Pic(O₄)→Pic(O_K) is that order-six group. Therefore the maximal-class unaveraged period of the averaged vector is exactly
~~~
Σ_{a∈Pic(O_K)} \bar F_d(a) = P₄(d;F) / 6.
~~~
There is no moving class-number or regulator factor. For d=323 the nonzero residue P₄=9 proves that the algebraic period and this averaged vector are nonzero in characteristic zero. Every eligible d has the same unramified local 2-torus and the same exact pair L=Z₂+4Z₂ω⊂L'=Z₂+(1/4)Z₂ω in its normalized local frame. These configurations are conjugate in GL₂(Q₂); the fixed local level vector is carried to the same line, with its norm preserved. Thus the ratio of the nonzero projected local norm to the original one is the same for every d. No use is made of the opposite-twist conductor of the mod-13 level-raising lift g, which need not be inherited just from E₋₁.

## The precise Waldspurger input

Use [Cai–Shu–Tian, Definition 1.7, Theorem 1.8, §2.2 and Lemma 3.4](https://arxiv.org/pdf/1408.1733), for **trivial** toric character: its conductor c and the reduced c₁ are both the unit ideal, even though the unaveraged input marks use O₄. The bad nonsplit set Σ₁ is {2,53}. At both these places definition 1.7 demands torus invariance, not invariance under a mismatched level Eichler compact at 2. It holds at 2 for the explicit averaged vector, and at 53 because the local compact is the maximal division order, with the inert torus units inside and uniformizer rational. At 3 the torus is split with the actual standard cyclic level-3 line. At all other finite places the vector is maximal-order fixed with the unramified trivial toric character. At infinity the minimal definite representation has the ordinary weight-two trivial archimedean factor.

For the local epsilon identity: at 2 the quadratic character is unramified, and the twist sign is multiplied by (−1)^4=+1; at 3 the two equal local factors multiply to +1; at 53 the inert unramified character changes the Steinberg sign; at good ramified primes the Gauss product with trivial central character gives η_v(−1); at the other good finite places the identity is +1. At infinity η_∞(−1)=−1 and the sign-twisted weight-two discrete parameter is isomorphic to itself. Thus the prescribed division places are precisely 53 and ∞. The choices meet CST's hypotheses, with D_K=−d prime to the level, no varying removed finite Euler factor. The appropriate admissible order at 2 can be taken as O_{K,2}+4M₂(Z₂) with discriminant exponent four and maximal torus intersection, not the input CM4 Eichler order. Lemma 3.4 gives its local type. That compact type, the other level compacts, and the Petersson norm ratio of the fixed torus projection are independent of d, so the CST U-level norm (the Petersson norm times the fixed compact mass factor of §2.2) is constant as well. There is no assumption that the averaged vector is a map on the original split modular curve.

Consequently the only varying external factor for |P₄(d;F)|² is √d, times the central value L(1,g_K)=L(1,g)L(1,g⊗χ₋d) in classical normalization. The reference d=323 shows that neither fixed L(1,g) nor the reference central value vanishes. All gamma factors are fixed. On the other hand [Sirolli–Tornaría, §§4–5, 8–9, Theorem 9.2](https://arxiv.org/html/2107.04483) and the existing nonzero +37 auxiliary give exactly L(1,g⊗χ₋d) proportional to the absolute square of the fixed negative coefficient divided by √d on this one discriminant type. The term 2^{ω(D,N)} is 1 here. Overlap with the fixed auxiliary is already covered by the earlier use of their Theorem B/Prop. 8.1. We obtain the exact characteristic-zero equality of ratios of squares
~~~
P₄(d;F)² / P₄(323;F)²
  = |a⁻₃₇(d)|² / |a⁻₃₇(323)|².
~~~
Here F is taken real; relative orientation changes only the squared ratio. This equality includes central zeros, by the formula on both sides.

## One algebraic reduction, no new unit assumptions

At each d the negative type-II quartic factor at 53 has the two values ±a single fourth-root-of-unity phase on the two polarizations, all other weights being real. Thus removing the common phase in the old exact source does not change the true algebraic complex-conjugate product, whose reduction is A⁻₃₇(d)² at the **same** coefficient place. All periods and weighted coefficients prior to taking ratios are integral there by the pinned F and unit weights. At d=323 the period residue is 9 and the phase-normalized negative coefficient is 12, both units; the ratio of their squares is 3 mod13. Hence (2Λ_d)²=3·A⁻₃₇(d)², equivalently Λ_d²=4·A⁻₃₇(d)². This argument needs no optimality assertion at a new modulus or at a second place over 13.

The exact bounded check compares all four previously accepted substitute-scalar reads plus d=35,1931,2579. In particular the previously matched local-symbol zero/unit pair 1931/2579 also gives direct 0/11, and negative 0/1. The zero does not prove characteristic-zero torsion or nonexistence of a rational point. Neither the calibration nor the comparison resolves joint nonvanishing at A⁻₃₇(Rq), A⁻₃₇(Rθq) on the genuine ray.

~~~sh
python3 -B compare_seven_exact_controls.py | cmp - EXACT-SEVEN-DIRECT-NEGATIVE-COMPARISONS.json
~~~
The replay uses the frozen q29 and low-map books, the existing weighted coefficient donor files and relative original tree. The extended calibration only removes the nonzero precondition and permits the bounded additional discriminants; no orientation or finite-arithmetic rule is changed.
