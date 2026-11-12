module
public import OpenFunctionField318
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public section
noncomputable section
namespace DominantFunctionField318
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f:X⟶Y) [IsDominant f]

theorem generic_eq : f (genericPoint X)=genericPoint Y:=by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ,f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- The actual pullback of generic-point stalks of a dominant morphism. -/
@[expose] def map : Y.functionField⟶X.functionField:=
  (Y.presheaf.stalkCongr (Inseparable.of_eq (generic_eq f))).inv≫f.stalkMap (genericPoint X)

lemma preimage_nonempty (U:Y.Opens) [Nonempty U]:Nonempty (f⁻¹ᵁU):=by
  refine ⟨⟨genericPoint X,?_⟩⟩
  change f (genericPoint X)∈U
  rw [generic_eq]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- Exact naturality on every actual section germ. -/
theorem map_germ (U:Y.Opens) [Nonempty U] [Nonempty (f⁻¹ᵁU)]:
    Y.germToFunctionField U≫map f=f.app U≫X.germToFunctionField (f⁻¹ᵁU):=by
  dsimp only [map]
  rw [←Category.assoc]
  change (Y.presheaf.germ U (genericPoint Y) _≫
    (Y.presheaf.stalkCongr _).inv)≫_=_
  rw [TopCat.Presheaf.stalkCongr_inv,Y.presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint X) _

theorem map_open [IsOpenImmersion f]:map f=(OpenFunctionField318.fieldIso f).hom:=rfl

variable {Z:Scheme.{u}} [IrreducibleSpace Z] (g:Y⟶Z) [IsDominant g]
/-- Composition is proved on all actual section germs. -/
theorem map_comp : map (f≫g)=map g≫map f:=by
  apply Z.presheaf.stalk_hom_ext
  intro U hU
  letI:Nonempty U:=⟨⟨genericPoint Z,hU⟩⟩
  letI:Nonempty (g⁻¹ᵁU):=preimage_nonempty g U
  letI:Nonempty (f⁻¹ᵁ(g⁻¹ᵁU)):=preimage_nonempty f (g⁻¹ᵁU)
  letI:Nonempty ((f≫g)⁻¹ᵁU):=preimage_nonempty (f≫g) U
  change Z.germToFunctionField U≫map (f≫g)=Z.germToFunctionField U≫map g≫map f
  rw [map_germ,←Category.assoc,map_germ,Category.assoc,map_germ,Scheme.Hom.comp_app,Category.assoc]
  rfl
end DominantFunctionField318
