module
public import SelectedOriginalCompactClassicalDifferentials318
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial KaehlerDifferential
open SelectedRationalRootCompactInstall318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryGeometry318 SelectedOriginalCompactClassicalDifferentials318
open SelectedIntrinsicBaseLinear318 SelectedIntrinsicGlobalToAffine318

namespace SelectedRationalCompactIntrinsicCoefficient318

variable (M : ℕ) [NeZero M] (p : (OpenJModel318.Base M)[X])
local notation "QS" => ordinaryRoot M p

variable (hp : p.Monic) (hu : IsUnit (AdjoinRoot.mk p p.derivative))
variable (hf : IsField (genericRoot M p))

abbrev compactStructure := compactJ M p hf ≫ ProjectiveJLine318.structureMap ℚ
abbrev RationalSections := Sections (compactStructure M p hf)

private theorem restrict_constant {X : Scheme}
    (i : Spec (CommRingCat.of QS)⟶X) [IsOpenImmersion i]
    (f : X⟶Spec (CommRingCat.of ℚ))
    (hi : i≫f=Spec.map (CommRingCat.ofHom (algebraMap ℚ QS))) (r : ℚ) :
    restrictRegular i (constants f r)=algebraMap ℚ QS r := by
  have h :
      ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ f.appTop) ≫ i.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of QS)).hom =
      CommRingCat.ofHom (algebraMap ℚ QS) := by
    rw [Category.assoc,←Category.assoc f.appTop,←Scheme.Hom.comp_appTop,hi,
      Scheme.ΓSpecIso_naturality,←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  exact congrArg (fun k => k r) h

include hp hu in
/-- The true rational compact differential restricted to the actual
ordinary open and expressed in that open's normalized dJ. -/
def rationalCoefficient : RationalSections M p hf→ₗ[ℚ]QS where
  toFun w := ordinaryFrame M p hp hu
    (restrict (ordinaryEmbedding M p hf hp hu) (compactStructure M p hf)
      (by letI : Fact p.Monic := ⟨hp⟩; exact actual_ordinary_Q M p hu hf) w)
  map_add' x y := by rw [map_add,map_add]
  map_smul' r w := by
    rw [RingHom.id_apply]
    change ordinaryFrame M p hp hu
      (restrict (ordinaryEmbedding M p hf hp hu) (compactStructure M p hf)
        _ (constants (compactStructure M p hf) r • w)) = _
    rw [restrict_smul,restrict_constant M p,map_smul,smul_eq_mul,Algebra.smul_def]

theorem rationalCoefficient_apply
    (hq : ordinaryEmbedding M p hf hp hu ≫ compactStructure M p hf =
      Spec.algebraMap ℚ (ordinaryRoot M p))
    (w : RationalSections M p hf) :
    rationalCoefficient M p hp hu hf w =
      ordinaryFrame M p hp hu
        (restrict (ordinaryEmbedding M p hf hp hu) (compactStructure M p hf) hq w) := rfl

end SelectedRationalCompactIntrinsicCoefficient318

#print axioms SelectedRationalCompactIntrinsicCoefficient318.rationalCoefficient
