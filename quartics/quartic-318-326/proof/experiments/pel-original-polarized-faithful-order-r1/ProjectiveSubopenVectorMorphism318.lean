module
public import ProjectiveSubopenRatioAtlas318
public import ComplexProjectiveRegularVectorPoints318
public import ComplexProjectivePointEquality318
public import ReducedComplexPointMorphisms318
public section
noncomputable section
namespace ProjectiveSubopenVectorMorphism318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
open ProjectivePreimageRegularRatios318
variable {ι : Type*} [Finite ι] {X : Scheme} [IsReduced X]
local instance standardGrading : GradedAlgebra (grading (ι := ι)) := MvPolynomial.gradedAlgebra
variable (f : X ⟶ Proj (grading (ι := ι)))
  (π : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType π]
  (hf : f ≫ ComplexProjectiveBase318.structureMap = π)
  (hpoints : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p ≫ π = 𝟙 _ →
    ∃ v : ι → ℂ, ∃ hv : ∃ i,v i≠0, p ≫ f = ComplexProjectiveSchemePoint318.point v hv)
  (U : X.Opens) (j : ι) (hU : U ≤ sourceOpen f j)

lemma span_top : Ideal.span (Set.range (ProjectiveSubopenRatioAtlas318.ratio f U j hU))=⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self j))
  rw [ProjectiveSubopenRatioAtlas318.ratio_self]
  exact isUnit_one

/-- Genuine projective morphism obtained from the normalized full vector
of regular functions on an arbitrary source subopen. -/
@[expose] def morphism : U.toScheme ⟶ Proj (grading (ι := ι)) :=
  ComplexProjectiveRegularVector318.morphism (U.ι ≫ π)
    (ProjectiveSubopenRatioAtlas318.ratio f U j hU) (span_top f U j hU)

include hf hpoints in
/-- The actual regular-vector construction equals the restriction of the
original projective scheme morphism. Reduced finite-type comparison
uses all C-points; this is not a set-level replacement of scheme equality. -/
theorem morphism_eq : morphism f π U j hU = U.ι ≫ f := by
  letI : LocallyOfFiniteType (U.ι ≫ π) := by infer_instance
  apply ReducedComplexPointMorphisms318.ext (U.ι ≫ π)
    ComplexProjectiveBase318.structureMap _ _
    (ComplexProjectiveRegularVector318.over_complex _ _ _)
    (by rw [Category.assoc,hf])
  intro p hp
  obtain ⟨v,hv,he⟩ := hpoints (p ≫ U.ι) (by simpa only [Category.assoc] using hp)
  let q := p ≫ X.homOfLE hU
  have hq : q ≫ (sourceOpen f j).ι ≫ f = ComplexProjectiveSchemePoint318.point v hv := by
    simpa only [q,Category.assoc,Scheme.homOfLE_ι_assoc] using he
  have hj := point_coordinate_nonzero f j q v hv hq
  have hb : q ≫ (sourceOpen f j).ι ≫ π = 𝟙 _ := by
    simpa only [q,Category.assoc,Scheme.homOfLE_ι_assoc] using hp
  have hc (i : ι) : ComplexProjectiveRegularVector318.pointVector
      (ProjectiveSubopenRatioAtlas318.ratio f U j hU) p i = v i/v j := by
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appTop (ratioSection f j i)) = _
    exact evaluation f π hf j i q hb v hv hj hq
  rw [morphism,ComplexProjectiveRegularVectorPoints318.point_action _ _ _ p hp,
    ←Category.assoc,he]
  apply ComplexProjectivePointEquality318.scheme_point_eq
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(v j)⁻¹,?_⟩
  funext i
  change (v j)⁻¹*v i=ComplexProjectiveRegularVector318.pointVector _ p i
  rw [hc,div_eq_mul_inv,mul_comm]
end ProjectiveSubopenVectorMorphism318
