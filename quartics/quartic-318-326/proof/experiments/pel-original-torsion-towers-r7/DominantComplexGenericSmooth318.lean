module
public import DominantFunctionField318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace DominantComplexGenericSmooth318
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
variable (π : Y ⟶ Spec (CommRingCat.of ℂ)) (f : X ⟶ Y) [IsDominant f]
  [LocallyOfFinitePresentation f]

/-- The actual generic field of a complex scheme has characteristic zero
through its original structural map and genuine generic germ. -/
lemma field_charZero : CharZero Y.functionField := by
  let c : ℂ →+* Y.functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ π.appTop ≫
      Y.germToFunctionField ⊤).hom
  exact c.charZero

/-- Generic smoothness for the actual dominant map of integral complex
schemes. The proof uses its literal generic-stalk map, not a transported
or analytically identified function field. -/
lemma generic_mem : genericPoint X ∈ f.smoothLocus := by
  rw [Scheme.Hom.mem_smoothLocus]
  letI : CharZero Y.functionField := field_charZero π
  let e := (Y.presheaf.stalkCongr
    (Inseparable.of_eq (DominantFunctionField318.generic_eq f))).inv
  have ht : (DominantFunctionField318.map f).hom.EssFiniteType := by
    change (e ≫ f.stalkMap (genericPoint X)).hom.EssFiniteType
    rw [CommRingCat.hom_comp]
    exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso e
      (f.stalkMap (genericPoint X))).mpr (LocallyOfFiniteType.stalkMap f _)
  have hm : (DominantFunctionField318.map f).hom.FormallySmooth := by
    algebraize [(DominantFunctionField318.map f).hom]
    exact Algebra.FormallySmooth.of_perfectField
  change (e ≫ f.stalkMap (genericPoint X)).hom.FormallySmooth at hm
  rw [CommRingCat.hom_comp] at hm
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso e
    (f.stalkMap (genericPoint X))).mp hm
end DominantComplexGenericSmooth318
