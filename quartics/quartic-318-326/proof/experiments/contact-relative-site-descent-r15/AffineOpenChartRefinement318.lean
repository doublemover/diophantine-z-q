module
public import AffineOpenChartDescent318
public section
noncomputable section
namespace AffineOpenChartRefinement318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open AffineFaithfullyFlatChart318
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
  (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)

/-- Both refinement maps are induced by the original sheaf restrictions. -/
abbrev baseMap : Spec Γ(Y, V) ⟶ Spec Γ(Y, U) :=
  Spec.map (Y.presheaf.map (homOfLE h).op)
abbrev sourceMap : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Spec Γ(X, f ⁻¹ᵁ U) :=
  Spec.map (X.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun x hx => h hx)).op)

lemma base_fromSpec : baseMap U V h ≫ base U hU = base V hV :=
  hU.map_fromSpec hV (homOfLE h).op
lemma source_fromSpec : sourceMap f U V h ≫ source f U hU = source f V hV :=
  (hU.preimage f).map_fromSpec (hV.preimage f) (homOfLE
    (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun x hx => h hx)).op

include hU hV in
/-- This is the original commuting chart square. Its proof uses the
actual chart immersions, which are monomorphisms, and original sections. -/
lemma square : sourceMap f U V h ≫ map f U = map f V ≫ baseMap U V h := by
  apply (cancel_mono (base U hU)).mp
  rw [Category.assoc, ← AffineFaithfullyFlatChart318.square, ← Category.assoc,
    source_fromSpec, Category.assoc, base_fromSpec, AffineFaithfullyFlatChart318.square]

lemma base_composition (W : Y.Opens) (k : W ≤ V) :
    baseMap V W k ≫ baseMap U V h = baseMap U W (k.trans h) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (Y.presheaf.map_comp (homOfLE h).op (homOfLE k).op).symm
lemma source_composition (W : Y.Opens) (k : W ≤ V) :
    sourceMap f V W k ≫ sourceMap f U V h = sourceMap f U W (k.trans h) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (X.presheaf.map_comp
    (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun x hx => h hx)).op
    (homOfLE (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V from fun x hx => k hx)).op).symm

end AffineOpenChartRefinement318
