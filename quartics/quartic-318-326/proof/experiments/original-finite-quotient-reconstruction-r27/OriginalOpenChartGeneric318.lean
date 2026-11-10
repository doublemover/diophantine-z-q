module
public import OriginalGenericStalkNaturality318
public import ActualOpenFractionField318
public section
noncomputable section
namespace OriginalOpenChartGeneric318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y] {A : Type} [CommRing A] [IsDomain A]
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
/-- A nonempty integral affine open contains the original generic point. -/
instance open_dominant : IsDominant j := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  have hc := genericPoint_spec Y
  rw [isGenericPoint_def] at hc
  rw [← hc]
  apply closure_mono
  intro y hy
  have he : y = genericPoint Y := Set.mem_singleton_iff.mp hy
  subst y
  exact ⟨genericPoint (Spec (CommRingCat.of A)), genericPoint_eq_of_isOpenImmersion j⟩

local instance actualAlgebra : Algebra A Y.functionField := ActualOpenFractionField318.sourceAlgebra j

/-- The fraction embedding specified by the ORIGINAL open chart has the
literal canonical generic point as its composite, not merely the same image. -/
theorem generic_square :
    Spec.map (CommRingCat.ofHom (algebraMap A Y.functionField)) ≫ j =
      OriginalGenericStalkNaturality318.generic Y := by
  haveI : IsIso (DominantFunctionField318.map j) :=
    inferInstanceAs (IsIso (OpenFunctionField318.fieldIso j).hom)
  apply (cancel_epi (Spec.map (DominantFunctionField318.map j))).mp
  rw [← Category.assoc, ← Spec.map_comp,
    ← OriginalGenericStalkNaturality318.naturality j]
  have h : CommRingCat.ofHom (algebraMap A Y.functionField) ≫
      DominantFunctionField318.map j =
        CommRingCat.ofHom (algebraMap A (Spec (CommRingCat.of A)).functionField) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact (ActualOpenFractionField318.genericAlgEquiv j).commutes
  rw [h]
  congr 1
  exact (Scheme.Spec.fromSpecStalk_eq' (CommRingCat.of A) _).symm
end OriginalOpenChartGeneric318
