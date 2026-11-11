module
public import DominantFunctionField318
public import SchematicEqualityExtension318
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public section
noncomputable section
namespace OriginalGenericStalkNaturality318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable (X : Scheme) [IrreducibleSpace X]

/-- The literal generic-stalk morphism of the ORIGINAL scheme. -/
@[expose] def generic : Spec X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)

instance generic_mono : Mono (generic X) := inferInstanceAs (Mono (X.fromSpecStalk _))

instance generic_dominant : IsDominant (generic X) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  have hc := genericPoint_spec X
  rw [isGenericPoint_def] at hc
  rw [← hc]
  apply closure_mono
  intro x hx
  have he : x = genericPoint X := Set.mem_singleton_iff.mp hx
  subst x
  exact ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)),
    Scheme.fromSpecStalk_closedPoint⟩

variable {X} {Y : Scheme} [IrreducibleSpace Y]

/-- Exact naturality of the ORIGINAL generic-stalk map for every dominant
scheme morphism, including the original generic-point transport. -/
@[reassoc] theorem naturality (f : X ⟶ Y) [IsDominant f] :
    generic X ≫ f = Spec.map (DominantFunctionField318.map f) ≫ generic Y := by
  unfold DominantFunctionField318.map generic
  rw [Spec.map_comp,Category.assoc,TopCat.Presheaf.stalkCongr_inv,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- Identity on the same generic stalk; obtained by exact Spec faithfulness
and cancellation through the actual generic morphism. -/
theorem map_id : DominantFunctionField318.map (𝟙 X) = 𝟙 X.functionField := by
  have h : Spec.map (DominantFunctionField318.map (𝟙 X)) = 𝟙 (Spec X.functionField) := by
    apply (cancel_mono (generic X)).mp
    simpa only [Category.id_comp,Category.comp_id] using (naturality (𝟙 X)).symm
  apply Spec.map_injective
  simpa using h

variable [IsIntegral X]

/-- Actual field pullback equality detects original scheme maps over a
separated base, using schematic density rather than an assumed faithful
representation of the deck group. -/
theorem maps_equal {B : Scheme} (s : Y ⟶ B) [IsSeparated s]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g]
    (hover : f ≫ s = g ≫ s)
    (hfield : DominantFunctionField318.map f = DominantFunctionField318.map g) : f = g := by
  letI : IsSchemeTheoreticallyDominant (generic X) :=
    IsSchemeTheoreticallyDominant.of_isDominant (generic X)
  apply SchematicEqualityExtension318.ext s hover (generic X)
  rw [naturality,naturality,hfield]

/-- On a field spectrum the actual generic-stalk morphism is the inverse
of the standard closed-stalk isomorphism; no replacement generic point. -/
theorem generic_field_isIso (K : CommRingCat) [Field K] : IsIso (generic (Spec K)) := by
  have hc : genericPoint (Spec K) = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  change IsIso ((Spec K).fromSpecStalk (genericPoint (Spec K)))
  rw [hc,← Scheme.Spec_stalkClosedPointIso]
  infer_instance

/-- The canonical generic-stalk morphism of the SAME original integral
scheme induces an actual function-field isomorphism. This supplies the
birational input of the reconstruction endpoint, rather than assuming it. -/
theorem generic_functionField_isIso : IsIso (DominantFunctionField318.map (generic X)) := by
  have hm : Spec.map (DominantFunctionField318.map (generic X)) =
      generic (Spec X.functionField) := by
    apply (cancel_mono (generic X)).mp
    exact (naturality (generic X)).symm
  haveI : IsIso (generic (Spec X.functionField)) := generic_field_isIso X.functionField
  haveI : IsIso (Spec.map (DominantFunctionField318.map (generic X))) := by
    rw [hm]
    infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact isIso_SpecMap_iff.mp inferInstance
end OriginalGenericStalkNaturality318
