module
public import ComplexProjectiveRegularVector318
public section
noncomputable section
namespace ComplexProjectiveRegularVectorPoints318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
open ComplexProjectiveRegularVector318
variable {ι : Type*} {X : Scheme}
local instance standardGrading : GradedAlgebra (grading (ι := ι)) := MvPolynomial.gradedAlgebra

lemma pointVector_nonzero (u : ι → Γ(X,⊤)) (hu : Ideal.span (Set.range u)=⊤)
    (p : ComplexPoint ⟶ X) : ∃ i, pointVector u p i≠0 := by
  by_contra h
  push_neg at h
  let e : Γ(X,⊤) →+* ℂ :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp p.appTop.hom
  have hk : Ideal.span (Set.range u) ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro a ⟨i,rfl⟩
    exact h i
  have hone : (1 : Γ(X,⊤)) ∈ Ideal.span (Set.range u) := by rw [hu]; trivial
  have he := hk hone
  change e 1=0 at he
  exact one_ne_zero (by simpa only [map_one] using he)

/-- Full homogeneous prime test for composition with an arbitrary actual
C-valued source point. This follows from pullback of REGULAR basic opens,
not merely agreement of an independently transported point map. -/
lemma positive_homogeneous_mem_iff (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤))
    (hu : Ideal.span (Set.range u)=⊤) (p : ComplexPoint ⟶ X) (hp : p≫π=𝟙 _)
    (x : ComplexPoint) (q : MvPolynomial ι ℂ) (n : ℕ)
    (hn : 0<n) (hq : q.IsHomogeneous n) :
    q ∈ ((p≫morphism π u hu) x).asHomogeneousIdeal ↔
      MvPolynomial.eval (pointVector u p) q=0 := by
  have he : p.appTop (evaluation π u q)=
      ComplexProjectiveSchemePoint318.evaluation (pointVector u p) q :=
    RingHom.congr_fun (point_evaluation π u p hp) q
  have hm : ((p≫morphism π u hu) x) ∈ Proj.basicOpen grading q ↔
      MvPolynomial.eval (pointVector u p) q≠0 := by
    change x ∈ ((p≫morphism π u hu) ⁻¹ᵁ Proj.basicOpen grading q) ↔ _
    rw [Scheme.Hom.comp_preimage,homogeneous_preimage π u hu q n hn hq,
      Scheme.preimage_basicOpen_top,he]
    by_cases h : MvPolynomial.eval (pointVector u p) q=0
    · have hz : ComplexProjectiveSchemePoint318.evaluation (pointVector u p) q=0 := by
        change ComplexProjectiveSchemePoint318.scalar
          (MvPolynomial.eval (pointVector u p) q)=0
        rw [h,map_zero]
      rw [hz]
      simp [h]
    · have hi : IsUnit (ComplexProjectiveSchemePoint318.evaluation (pointVector u p) q) := by
        change IsUnit (ComplexProjectiveSchemePoint318.scalar
          (MvPolynomial.eval (pointVector u p) q))
        exact (isUnit_iff_ne_zero.mpr h).map ComplexProjectiveSchemePoint318.scalar
      rw [Scheme.basicOpen_of_isUnit _ hi]
      simp [h]
  change (q∉((p≫morphism π u hu) x).asHomogeneousIdeal ↔
    MvPolynomial.eval (pointVector u p) q≠0) at hm
  simpa only [not_not] using not_congr hm

lemma underlying_point (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤))
    (hu : Ideal.span (Set.range u)=⊤) (p : ComplexPoint ⟶ X) (hp : p≫π=𝟙 _)
    (x : ComplexPoint) :
    (p≫morphism π u hu) x=
      ComplexProjectiveMarkerPoint318.point (pointVector u p) (pointVector_nonzero u hu p) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n q hq
  obtain ⟨i,hi⟩ := pointVector_nonzero u hu p
  have hiI : MvPolynomial.X i∉((p≫morphism π u hu) x).asHomogeneousIdeal := by
    rw [positive_homogeneous_mem_iff π u hu p hp x _ 1 (by norm_num)
      (MvPolynomial.isHomogeneous_X ℂ i)]
    simpa using hi
  have hm := positive_homogeneous_mem_iff π u hu p hp x (q*MvPolynomial.X i) (n+1)
    (Nat.zero_lt_succ n) (hq.mul (MvPolynomial.isHomogeneous_X ℂ i))
  rw [((p≫morphism π u hu) x).isPrime.mul_mem_iff_mem_or_mem] at hm
  simp only [hiI,or_false,map_mul,MvPolynomial.eval_X,mul_eq_zero,hi,or_false] at hm
  exact hm.trans (ComplexProjectiveMarkerPoint318.homogeneous_mem_iff
    (pointVector u p) (pointVector_nonzero u hu p) q n hq).symm

/-- Exact equality of genuine Spec(C)-valued morphisms, with their
original structural C maps. Finite type of polynomial Proj justifies
closed-point uniqueness; no equality-of-points implies scheme-map
principle is asserted for arbitrary sources. -/
theorem point_action [Finite ι] (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤))
    (hu : Ideal.span (Set.range u)=⊤) (p : ComplexPoint ⟶ X) (hp : p≫π=𝟙 _) :
    p≫morphism π u hu=ComplexProjectiveSchemePoint318.point
      (pointVector u p) (pointVector_nonzero u hu p) := by
  apply ext_of_apply_closedPoint_eq ComplexProjectiveBase318.structureMap
  · rw [Category.assoc,over_complex,hp]
  · exact ComplexProjectiveBase318.point_over _ _
  · exact (underlying_point π u hu p hp _).trans
      (ComplexProjectiveSchemePoint318.underlying_point _ _ _).symm
end ComplexProjectiveRegularVectorPoints318
