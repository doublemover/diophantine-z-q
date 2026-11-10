module
public import LocalSheafCohomologyAdditive318
public section
noncomputable section
namespace LocalCohomologyRestriction318
open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 LocalSheafCohomologyAdditive318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}}
abbrev freeMap {U V : Opens X} (f : U ⟶ V) : freePresheaf U ⟶ freePresheaf V :=
  Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free
abbrev generatorMap {U V : Opens X} (f : U ⟶ V) : generator U ⟶ generator V :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map (freeMap f)

theorem presheaf_naturality (F : ASheaf (X:=X)) {U V : Opens X} (f : U ⟶ V)
    (a : freePresheaf V ⟶ F.obj) :
    presheafEquiv F U (freeMap f ≫ a) = F.obj.map f.op (presheafEquiv F V a) := by
  have h := ConcreteCategory.congr_hom (a.naturality f.op) (FreeAbelianGroup.of (𝟙 V))
  simpa [presheafEquiv,freeMap,freePresheaf] using h

theorem section_naturality (F : ASheaf (X:=X)) {U V : Opens X} (f : U ⟶ V)
    (a : generator V ⟶ F) :
    sectionEquiv F U (generatorMap f ≫ a) = F.obj.map f.op (sectionEquiv F V a) := by
  exact (congrArg (presheafEquiv F U)
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv_naturality_left
      (freeMap f) a)).trans (presheaf_naturality F f _)

theorem zero_naturality (F : ASheaf (X:=X)) {U V : Opens X} (f : U ⟶ V)
    (x : F.H' 0 V) :
    zeroAddEquiv F U ((F.cohomologyPresheaf 0).map f.op x) =
      F.obj.map f.op (zeroAddEquiv F V x) := by
  have h : Ext.homEquiv₀ ((Ext.mk₀ (generatorMap f)).comp x (zero_add 0)) =
      generatorMap f ≫ Ext.homEquiv₀ x := by
    apply (Ext.mk₀_bijective _ _).injective
    simp only [Ext.mk₀_homEquiv₀_apply,← Ext.mk₀_comp_mk₀]
  exact (congrArg (sectionEquiv F U) h).trans (section_naturality F f (Ext.homEquiv₀ x))
end LocalCohomologyRestriction318
