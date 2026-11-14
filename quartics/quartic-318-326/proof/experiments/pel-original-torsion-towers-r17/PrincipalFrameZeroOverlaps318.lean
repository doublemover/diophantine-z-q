module
public import PrincipalIdealOpenRestriction318
public import CompatibleClosedOverlap318
public import IntegralOpenIntersection318
public import OriginalOpenCoefficientSpecialization318
public section
noncomputable section
namespace PrincipalFrameZeroOverlaps318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PrincipalIdealOpenRestriction318
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (c : ∀ i,Γ(X,U i)) (t : ∀ i j,Γ(X,U i ⊓ U j)ˣ)
  (hc : ∀ i j,X.presheaf.map (homOfLE inf_le_left).op (c i)=
    (t i j).val*X.presheaf.map (homOfLE inf_le_right).op (c j))
@[expose] def coefficient (i : ι) : Γ((U i).toScheme,⊤) := (LineFrameTopScalar318.ringTop (U i)).inv (c i)
abbrev ideal (i : ι) : (U i).toScheme.IdealSheafData := principal (coefficient U c i)
abbrev Zero (i : ι) : Scheme := (ideal U c i).subscheme
abbrev zeroInclusion (i : ι) : Zero U c i ⟶ (U i).toScheme := (ideal U c i).subschemeι
abbrev left (i j : ι) : (U i ⊓ U j).toScheme ⟶ (U i).toScheme := X.homOfLE inf_le_left
abbrev right (i j : ι) : (U i ⊓ U j).toScheme ⟶ (U j).toScheme := X.homOfLE inf_le_right
abbrev overlapIdeal (i j : ι) := (ideal U c i).comap (left U i j)
abbrev OverlapZero (i j : ι) : Scheme := (overlapIdeal U c i j).subscheme
abbrev overlapInclusion (i j : ι) : OverlapZero U c i j ⟶ (U i ⊓ U j).toScheme :=
  (overlapIdeal U c i j).subschemeι

lemma coefficient_restriction (i : ι) (W : X.Opens) (hW : W≤U i) :
    (X.homOfLE hW).appTop (coefficient U c i)=
      (LineFrameTopScalar318.ringTop W).inv (X.presheaf.map (homOfLE hW).op (c i)) := by
  have h := OriginalOpenCoefficientSpecialization318.coefficient_pullback (U i) W hW (coefficient U c i)
  simpa only [GlobalSectionFrameCoordinates318.coefficient,coefficient,Iso.inv_hom_id_apply] using h.symm

include hc in
/-- The entire principal IDEALS agree on the actual overlap, retaining
all nilpotents and multiplicities rather than only common zero sets. -/
lemma ideal_eq (i j : ι) : overlapIdeal U c i j=(ideal U c j).comap (right U i j) := by
  rw [overlapIdeal,ideal,comap_principal,ideal,comap_principal,
    coefficient_restriction,coefficient_restriction,hc,map_mul]
  let u := Units.map (LineFrameTopScalar318.ringTop (U i ⊓ U j)).inv.hom.toMonoidHom (t i j)
  exact principal_unit_mul u _

@[expose] def toLeft (i j : ι) : OverlapZero U c i j ⟶ Zero U c i :=
  ((ideal U c i).comapIso (left U i j)).hom≫pullback.snd _ _
@[expose] def toRight (i j : ι) : OverlapZero U c i j ⟶ Zero U c j :=
  eqToHom (congrArg Scheme.IdealSheafData.subscheme (ideal_eq U c t hc i j))≫
    ((ideal U c j).comapIso (right U i j)).hom≫pullback.snd _ _
@[reassoc] lemma left_square (i j : ι) :
    overlapInclusion U c i j≫left U i j=toLeft U c i j≫zeroInclusion U c i := by
  rw [toLeft,←Category.assoc,←pullback.condition,Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
@[reassoc] lemma right_square (i j : ι) :
    overlapInclusion U c i j≫right U i j=toRight U c t hc i j≫zeroInclusion U c j := by
  have h := ideal_eq U c t hc i j
  unfold toRight
  cases h
  rw [eqToHom_refl,Category.id_comp,←Category.assoc,←pullback.condition,Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

lemma left_cartesian (i j : ι) : IsPullback (overlapInclusion U c i j) (toLeft U c i j)
    (left U i j) (zeroInclusion U c i) := by
  apply isPullback_of_isClosedImmersion _ _ _ _ (left_square U c i j)
  simp only [Scheme.IdealSheafData.ker_subschemeι]
  rfl
lemma right_cartesian (i j : ι) : IsPullback (overlapInclusion U c i j) (toRight U c t hc i j)
    (right U i j) (zeroInclusion U c j) := by
  apply isPullback_of_isClosedImmersion _ _ _ _ (right_square U c t hc i j)
  simpa only [Scheme.IdealSheafData.ker_subschemeι] using (ideal_eq U c t hc i j).symm

abbrev into (i : ι) : Zero U c i ⟶ X := zeroInclusion U c i≫(U i).ι
lemma whole_cartesian (i j : ι) : IsPullback (toLeft U c i j) (toRight U c t hc i j)
    (into U c i) (into U c j) :=
  CompatibleClosedOverlap318.cartesian (U i).ι (U j).ι (left U i j) (right U i j)
    (zeroInclusion U c i) (zeroInclusion U c j) (overlapInclusion U c i j)
    (toLeft U c i j) (toRight U c t hc i j)
    (IntegralOpenIntersection318.cartesian (U i) (U j)).flip
    (left_cartesian U c i j) (right_cartesian U c t hc i j)

include hc in
lemma pullback_open (i j : ι) : IsOpenImmersion (pullback.fst (into U c i) (into U c j)) :=
  CompatibleClosedOverlap318.fst_open (U i).ι (U j).ι (left U i j) (right U i j)
    (zeroInclusion U c i) (zeroInclusion U c j) (overlapInclusion U c i j)
    (toLeft U c i j) (toRight U c t hc i j)
    (IntegralOpenIntersection318.cartesian (U i) (U j)).flip
    (left_cartesian U c i j) (right_cartesian U c t hc i j)

include hc in
/-- Full scheme-point range, needed to identify each chart as the
entire ambient-open base change after gluing. -/
lemma pullback_range (i j : ι) : Set.range (pullback.fst (into U c i) (into U c j))=
    (into U c i) ⁻¹' (U j : Set X) := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    have h := congrArg (fun f => f p) (pullback.condition (f := into U c i) (g := into U c j))
    change into U c i (pullback.fst _ _ p)∈U j
    rw [show into U c i (pullback.fst _ _ p)=into U c j (pullback.snd _ _ p) from h]
    exact (zeroInclusion U c j (pullback.snd _ _ p)).property
  · intro hx
    let w : (U i ⊓ U j).toScheme := ⟨(zeroInclusion U c i x).val,(zeroInclusion U c i x).property,hx⟩
    have hw : left U i j w=zeroInclusion U c i x := rfl
    obtain ⟨v,hv,hx'⟩ := Scheme.exists_preimage_of_isPullback (left_cartesian U c i j) w x hw
    let e := (whole_cartesian U c t hc i j).isoPullback
    refine ⟨e.hom v,?_⟩
    rw [←Scheme.Hom.comp_apply,(whole_cartesian U c t hc i j).isoPullback_hom_fst]
    exact hx'
end PrincipalFrameZeroOverlaps318
