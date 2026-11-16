module
public import SchemeUnramifiedLocus318
public import DominantComplexGenericSmooth318
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Etale.Field
public section
noncomputable section
namespace DominantComplexGenericUnramified318
open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- Localization of the actual source algebra preserves its finite fibers.
This supplies the missing full-localization input for native stalk maps. -/
lemma quasiFinite_localization : RingHom.HoldsForLocalization @RingHom.QuasiFinite := by
  introv R _
  rw [RingHom.quasiFinite_algebraMap]
  exact Algebra.QuasiFinite.of_isLocalization M

lemma stalk_quasiFinite {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) :
    (f.stalkMap x).hom.QuasiFinite :=
  HasRingHomProperty.stalkMap
    (fun f hf p q ↦ quasiFinite_localization.localRingHom
      RingHom.QuasiFinite.stableUnderComposition
      RingHom.QuasiFinite.isStableUnderBaseChange.localizationPreserves _ hf) ‹_› x

variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
variable (π : Y ⟶ Spec (CommRingCat.of ℂ)) (f : X ⟶ Y)
  [IsDominant f] [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
/-- The genuine generic field extension is finite by quasi-finiteness,
then separable in characteristic zero. No reduced-fiber inference is used. -/
lemma generic_mem : genericPoint X ∈ SchemeUnramifiedLocus318.locus f := by
  rw [SchemeUnramifiedLocus318.mem_locus]
  letI : CharZero Y.functionField := DominantComplexGenericSmooth318.field_charZero π
  let e := (Y.presheaf.stalkCongr
    (Inseparable.of_eq (DominantFunctionField318.generic_eq f))).inv
  have hq : (DominantFunctionField318.map f).hom.QuasiFinite := by
    change (e ≫ f.stalkMap (genericPoint X)).hom.QuasiFinite
    rw [CommRingCat.hom_comp]
    exact (RingHom.QuasiFinite.respectsIso.cancel_left_isIso e
      (f.stalkMap (genericPoint X))).mpr (stalk_quasiFinite f _)
  have hm : (DominantFunctionField318.map f).hom.FormallyUnramified := by
    algebraize [(DominantFunctionField318.map f).hom]
    letI : Module.Finite Y.functionField X.functionField := Module.Finite.of_quasiFinite
    exact Algebra.FormallyUnramified.of_isSeparable Y.functionField X.functionField
  change (e ≫ f.stalkMap (genericPoint X)).hom.FormallyUnramified at hm
  rw [CommRingCat.hom_comp] at hm
  exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso e
    (f.stalkMap (genericPoint X))).mp hm
end DominantComplexGenericUnramified318
