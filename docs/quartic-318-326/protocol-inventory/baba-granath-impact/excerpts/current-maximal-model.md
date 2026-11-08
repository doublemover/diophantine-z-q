# Binding the actual maximal Shimura stack to Yuan's isometry

## Exact role

This note closes the model-identification antecedent in the contact metric comparison. It binds the actual chosen quaternionic fiber surface to the universal Hodge determinant and to Yuan's integral Kodaira–Spencer isometry on the **maximal** stack. It is a mathematical application of the named PEL/moduli theorem, not a Lean formalization of stacks or Arakelov line bundles. Smooth curvature estimates, vertical extension of q0,q1, existence of an auxiliary integral section and stable-height normalization are independently reviewed by the converse worker; they are not claimed as new work here.

The output is the exact identity for the actual surface A at the chosen point y:

    h_{ω_max^⊗2}(y) = 2 h_Yuan(A) + log210,

and ordinary pullback of the two already constructed sections to that same line bundle at y. There is **no level-three degree or ramification correction** in this identity.

## 1. Match the quaternion algebra, order, and level

The geometric producer uses the indefinite rational quaternion algebra B with reduced discriminant210 and the maximal order O. This is the algebra defining X_210 and its four González–Rotger quotient models. It is not the coefficient D=11−6√2 of the separate elliptic encoding curve.

Fix μ0∈O with μ0²=−210. The standard quadratic-embedding criterion applies because Q(√−210) is nonsplit at every finite ramified place of B and at the real place B is split. An integral embedding lies in a maximal order; maximal orders of an indefinite quaternion algebra over Q are conjugate, so it can be put in the chosen O. The fiber producer has made this choice already. It determines the positive involution β↦μ0^−1 β^ι μ0, exactly as in Yuan's setup. It does not replace A by an isogenous variety.

Take U_max=Ohat^*. Yuan defines n(U) as the product of rational primes at which U_p is not maximal. Consequently n(U_max)=1, while d_B=210. His maximal moduli stack M therefore lives over **Z**, not merely Z[1/3] or Z[1/210]. Its objects are abelian surfaces with the actual O-action satisfying the determinant condition. The universal surface π:A_univ→M and Hodge determinant

    λ = det(e^* Ω^1_(A_univ/M))

are the ones in Yuan's theorem. His §2.1 gives this stack's regularity, properness and semistability and the automatic principal polarization for the fixed positive involution. The polarization is part of that theorem application, not an extra assumed bound on a polarization degree.

## 2. The actual full-level-three fiber maps to this stack

The earlier producer chooses a point of the **entire** fine principal-level-three scheme Y, lying above a rational point s of the five-contact quotient. Its fiber surface A, O-action i, and full level marking η are the actual data defined over the controlled normal fiber field L. Forgetting η gives

    (A,i,η) ∈ Y(L)  ↦  (A,i) ∈ M(L).

The underlying abelian surface is literally unchanged, rather than merely isogenous to the universal fiber. This is the morphism between the same PEL moduli problems, so the universal property gives a canonical identification

    A_univ ×_M Spec L ≅ A

compatible with O-actions, the identity sections and the chosen polarization. Smooth relative differentials commute with this base change; taking their top exterior power gives

    λ|_(Spec L) ≅ det H^0(A, Ω^1_A).

The same identification holds on any integral extension over which the point extends to the maximal stack. Thus the Hodge determinant used in the height calculation is the determinant for this **actual** surface A, not for a different model inferred from its coarse curve point.

The full level marking is used to construct a controlled definition field and universal fiber. It is then forgotten for this integral identity. One must not apply the nonmaximal-level theorem on Z[1/3] and simply pretend the result is a statement over Z. The maximal stack with n=1 is what supplies the factor210 at all primes.

## 3. Canonical line bundle and coarse coordinate

Let c:M_Q→X_210 be the coarse map. The quaternion curve has no elliptic stabilizers beyond its central automorphisms±1: the two elliptic corrections vanish for discriminant210, as checked in the fiber producer. The central involution acts trivially on the base tangent coordinate. Hence the canonical line of M_Q identifies with the pullback of the canonical line of the smooth coarse curve; this can be checked on an étale atlas. There is no extra orbifold divisor at a characteristic-zero point.

The functions s and t=32s are the previously fixed rational functions on the coarse curve, with the exact five branch values. Pulling those functions to M gives the same rational functions. Therefore

    q0 = (dt)² / ∏_(i=0)^3(t−a_i),        q1=t q0,
    (a_0,a_1,a_2,a_3)=(0,32,76832,−343).

The fifth branch value is infinity, not a factor of this four-term product. These are the actual rational sections of ω_M^⊗2 used in the metric/extension proof. The source's branch-coordinate calculation and semistable vertical argument establish that J²q0 and J²q1 extend to global sections on this **maximal** stack. This note does not reinterpret them as sections of ω_Y^⊗2 on a chosen integral level-three model.

At a characteristic-zero geometric point, the automorphism−1 acts as−1 on each of the two invariant differentials of A and hence as+1 on their determinant λ. It also acts trivially on ω_M. Thus the identity below is compatible with the central gerbe. It does not acquire a factor1/2 from global stack integration: we evaluate a line bundle on an actual object over a number field, not integrate its first Chern class over the stack.

## 4. Apply the precise integral Kodaira–Spencer map

Yuan's Theorem1.1 supplies a canonical injective map
