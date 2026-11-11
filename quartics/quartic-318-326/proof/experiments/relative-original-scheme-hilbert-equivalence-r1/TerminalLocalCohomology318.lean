module
public import LocalSheafCohomologySections318

public section
noncomputable section
namespace TerminalLocalCohomology318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 SheafInverseImageConstants318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : TopCat.{0})
abbrev sectionsFunctor (U : Opens X) :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op U) ⋙ forget AddCommGrpCat

@[expose] def generatorRepresents (U : Opens X) :
    (sectionsFunctor X U).CorepresentableBy (generator U) where
  homEquiv := sectionEquiv _ U
  homEquiv_comp a f := sectionEquiv_naturality a U f

@[expose] def integerSectionEquiv (F : ASheaf (X:=X)) :
    (integerSheaf X ⟶ F) ≃ F.obj.obj (op ⊤) :=
  (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homAddEquiv
    (AddCommGrpCat.of (ULift ℤ)) F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toEquiv

theorem integerSectionEquiv_naturality {F G : ASheaf (X:=X)} (a : F ⟶ G)
    (f : integerSheaf X ⟶ F) :
    integerSectionEquiv X G (f ≫ a) = a.hom.app (op ⊤) (integerSectionEquiv X F f) := by
  exact congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv_naturality_right f a)

@[expose] def integerRepresents : (sectionsFunctor X ⊤).CorepresentableBy (integerSheaf X) where
  homEquiv := integerSectionEquiv X _
  homEquiv_comp a f := integerSectionEquiv_naturality X a f

/-- The actual free-abelian generator at the terminal open is the original constant integer sheaf. -/
@[expose] def generatorIso : generator (⊤ : Opens X) ≅ integerSheaf X :=
  (generatorRepresents X ⊤).uniqueUpToIso (integerRepresents X)

/-- Precomposition with an actual coefficient-generator isomorphism is an additive Ext equivalence. -/
@[expose] def extEquivalence {A B : ASheaf (X:=X)} (e : A ≅ B)
    (F : ASheaf (X:=X)) (n : ℕ) : Ext A F n ≃+ Ext B F n where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,Iso.hom_inv_id,Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,Iso.inv_hom_id,Ext.mk₀_id_comp]
  map_add' x y := Ext.comp_add _ _ _ _

/-- Canonical local-to-global cohomology comparison at the full open, by the original representing objects. -/
@[expose] def equivalence (F : ASheaf (X:=X)) (n : ℕ) : F.H' n ⊤ ≃+ Sheaf.H F n :=
  extEquivalence X (generatorIso X) F n

end TerminalLocalCohomology318
