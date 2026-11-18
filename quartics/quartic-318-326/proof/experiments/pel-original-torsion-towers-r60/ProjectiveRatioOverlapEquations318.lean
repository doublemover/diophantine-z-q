module
public import ProjectivePreimageRegularRatios318
public import ReducedSchemeGlobalFunctionSeparation318
public section
noncomputable section
namespace ProjectiveRatioOverlapEquations318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
open ProjectivePreimageRegularRatios318
variable {ι : Type*} {X : Scheme} [IsReduced X]
local instance standardGrading : GradedAlgebra (grading (ι := ι)) := MvPolynomial.gradedAlgebra
variable (f : X ⟶ Proj (grading (ι := ι)))
  (π : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType π]
  (hf : f ≫ ComplexProjectiveBase318.structureMap = π)
  (hpoints : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p ≫ π = 𝟙 _ →
    ∃ v : ι → ℂ, ∃ hv : ∃ i,v i≠0, p ≫ f = ComplexProjectiveSchemePoint318.point v hv)

abbrev overlapOpen (j k : ι) : X.Opens := sourceOpen f j ⊓ sourceOpen f k
@[expose] def left (j k : ι) : (overlapOpen f j k).toScheme ⟶ (sourceOpen f j).toScheme :=
  X.homOfLE inf_le_left
@[expose] def right (j k : ι) : (overlapOpen f j k).toScheme ⟶ (sourceOpen f k).toScheme :=
  X.homOfLE inf_le_right
@[reassoc] lemma left_inclusion (j k : ι) :
    left f j k ≫ (sourceOpen f j).ι = (overlapOpen f j k).ι := Scheme.homOfLE_ι _
@[reassoc] lemma right_inclusion (j k : ι) :
    right f j k ≫ (sourceOpen f k).ι = (overlapOpen f j k).ι := Scheme.homOfLE_ι _

include π hf hpoints

/-- Actual equality of regular functions on the ENTIRE inverse-image
intersection. The only point input is a literal scheme-point formula
for f, and reduced finite-type separation turns it into a sheaf equation. -/
theorem transition (j k i : ι) :
    (left f j k).appTop (ratioSection f j i) =
      (right f j k).appTop (ratioSection f k i) *
        (left f j k).appTop (ratioSection f j k) := by
  let πW := (overlapOpen f j k).ι ≫ π
  letI : LocallyOfFiniteType πW := by dsimp [πW]; infer_instance
  apply ReducedSchemeGlobalFunctionSeparation318.ext πW
  intro p hp
  obtain ⟨v,hv,he⟩ := hpoints (p ≫ (overlapOpen f j k).ι) (by simpa only [Category.assoc] using hp)
  have hjpoint : (p ≫ left f j k) ≫ (sourceOpen f j).ι ≫ f =
      ComplexProjectiveSchemePoint318.point v hv := by
    simpa only [Category.assoc,left_inclusion_assoc] using he
  have hkpoint : (p ≫ right f j k) ≫ (sourceOpen f k).ι ≫ f =
      ComplexProjectiveSchemePoint318.point v hv := by
    simpa only [Category.assoc,right_inclusion_assoc] using he
  have hjbase : (p ≫ left f j k) ≫ (sourceOpen f j).ι ≫ π = 𝟙 _ := by
    simpa only [Category.assoc,left_inclusion_assoc] using hp
  have hkbase : (p ≫ right f j k) ≫ (sourceOpen f k).ι ≫ π = 𝟙 _ := by
    simpa only [Category.assoc,right_inclusion_assoc] using hp
  have hj := point_coordinate_nonzero f j _ v hv hjpoint
  have hk := point_coordinate_nonzero f k _ v hv hkpoint
  apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.injective
  rw [map_mul,map_mul]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((p ≫ left f j k).appTop (ratioSection f j i)) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((p ≫ right f j k).appTop (ratioSection f k i)) *
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((p ≫ left f j k).appTop (ratioSection f j k))
  rw [evaluation f π hf j i _ hjbase v hv hj hjpoint,
    evaluation f π hf k i _ hkbase v hv hk hkpoint,
    evaluation f π hf j k _ hjbase v hv hj hjpoint]
  field_simp [hj,hk]

/-- The transition is a genuine global regular UNIT on the whole
scheme intersection, including nonclosed points. -/
theorem transition_isUnit (j k : ι) :
    IsUnit ((left f j k).appTop (ratioSection f j k)) := by
  let πW := (overlapOpen f j k).ι ≫ π
  letI : LocallyOfFiniteType πW := by dsimp [πW]; infer_instance
  apply ReducedSchemeGlobalFunctionSeparation318.isUnit πW
  intro p hp
  obtain ⟨v,hv,he⟩ := hpoints (p ≫ (overlapOpen f j k).ι) (by simpa only [Category.assoc] using hp)
  have hjpoint : (p ≫ left f j k) ≫ (sourceOpen f j).ι ≫ f =
      ComplexProjectiveSchemePoint318.point v hv := by
    simpa only [Category.assoc,left_inclusion_assoc] using he
  have hkpoint : (p ≫ right f j k) ≫ (sourceOpen f k).ι ≫ f =
      ComplexProjectiveSchemePoint318.point v hv := by
    simpa only [Category.assoc,right_inclusion_assoc] using he
  have hjbase : (p ≫ left f j k) ≫ (sourceOpen f j).ι ≫ π = 𝟙 _ := by
    simpa only [Category.assoc,left_inclusion_assoc] using hp
  have hj := point_coordinate_nonzero f j _ v hv hjpoint
  have hk := point_coordinate_nonzero f k _ v hv hkpoint
  have hev := evaluation f π hf j k (p ≫ left f j k) hjbase v hv hj hjpoint
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (p.appTop ((left f j k).appTop (ratioSection f j k)))) := by
    rw [show p.appTop ((left f j k).appTop (ratioSection f j k)) =
      (p ≫ left f j k).appTop (ratioSection f j k) from rfl,hev]
    exact isUnit_iff_ne_zero.mpr (div_ne_zero hk hj)
  simpa only [←ConcreteCategory.comp_apply,Iso.hom_inv_id,ConcreteCategory.id_apply] using
    hu.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
end ProjectiveRatioOverlapEquations318
