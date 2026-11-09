module
public import InverseImageLocalCohomology318
public import Mathlib.CategoryTheory.Adjunction.Unique

public section
noncomputable section
namespace InverseImageTerminalCoherence318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 SheafInverseImageConstants318
open InverseImageLocalGenerator318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original terminal representing isomorphism has its specified section normalization. -/
theorem terminalHom_sections (X : TopCat.{0}) (F : ASheaf (X:=X))
    (a : integerSheaf X ⟶ F) :
    sectionEquiv F ⊤ ((TerminalLocalCohomology318.generatorIso X).hom ≫ a) =
      TerminalLocalCohomology318.integerSectionEquiv X F a := by
  rw [sectionEquiv_naturality]
  change a.hom.app (op ⊤)
    ((sectionEquiv _ ⊤) ((sectionEquiv _ ⊤).symm
      (TerminalLocalCohomology318.integerSectionEquiv X _ (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  simpa only [Category.id_comp] using
    (TerminalLocalCohomology318.integerSectionEquiv_naturality X a (𝟙 _)).symm

/-- Uniqueness of left adjoints identifies their hom equivalences, not only their objects. -/
theorem leftAdjointUniq_sections {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R)
    (x : C) (y : D) (g : L'.obj x ⟶ y) :
    a.homEquiv x y ((Adjunction.leftAdjointUniq a b).hom.app x ≫ g) =
      b.homEquiv x y g := by
  rw [a.homEquiv_naturality_right,Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The earlier integer-sheaf comparison is normalized by precisely the original section adjunction. -/
theorem integerIso_sections (F : ASheaf (X:=X)) (a : integerSheaf X ⟶ F) :
    TerminalLocalCohomology318.integerSectionEquiv Y ((directImage f).obj F)
      ((adjunction f).homEquiv _ _ ((integerIso f).hom ≫ a)) =
      TerminalLocalCohomology318.integerSectionEquiv X F a := by
  let A := (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{0} isTerminalTop).comp
      (adjunction f)).ofNatIsoRight (directImageGlobalSections f))
  let B := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop
  have he := leftAdjointUniq_sections A B (AddCommGrpCat.of (ULift ℤ)) F a
  have he' := congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _) he
  simpa only [A,B,Adjunction.homEquiv_ofNatIsoRight_apply,Adjunction.comp_homEquiv,
    Equiv.trans_apply,directImageGlobalSections,Iso.refl_hom,NatTrans.id_app,Category.comp_id]
    using he'

/-- The separately constructed local and integer generator comparisons have identical normalization. -/
theorem terminal_hom_coherence :
    (inverseImage f).map (TerminalLocalCohomology318.generatorIso Y).hom ≫ (integerIso f).hom =
      generatorHom f ⊤ ≫ (TerminalLocalCohomology318.generatorIso X).hom := by
  apply (sectionMate f ⊤ _).injective
  rw [generatorHom_section]
  change sectionEquiv ((directImage f).obj (integerSheaf X)) ⊤
      ((adjunction f).homEquiv _ _
        ((inverseImage f).map (TerminalLocalCohomology318.generatorIso Y).hom ≫
          (integerIso f).hom)) = _
  rw [(adjunction f).homEquiv_naturality_left,terminalHom_sections]
  have ht := terminalHom_sections X (integerSheaf X) (𝟙 _)
  rw [Category.comp_id] at ht
  rw [ht]
  simpa only [Category.comp_id] using integerIso_sections f (integerSheaf X) (𝟙 _)

/-- The inverse maps agree as well, in the exact direction used by Ext precomposition. -/
theorem terminal_inv_coherence :
    (integerIso f).inv ≫ (inverseImage f).map (TerminalLocalCohomology318.generatorIso Y).inv =
      (TerminalLocalCohomology318.generatorIso X).inv ≫ generatorInv f ⊤ := by
  let e₁ := ((inverseImage f).mapIso (TerminalLocalCohomology318.generatorIso Y)).trans
    (integerIso f)
  let e₂ := (InverseImageLocalGenerator318.generatorIso f ⊤).trans
    (TerminalLocalCohomology318.generatorIso X)
  have he : e₁ = e₂ := Iso.ext (terminal_hom_coherence f)
  exact congrArg (fun e => e.inv) he

/-- The new local-at-top derived comparison is exactly the original global comparison in every degree. -/
theorem comparison_terminal (F : ASheaf (X:=X)) (n : ℕ)
    (x : ((directImage f).obj F).H' n ⊤) :
    SourceCohomologyComparison318.comparison f F n
        (TerminalLocalCohomology318.equivalence Y ((directImage f).obj F) n x) =
      TerminalLocalCohomology318.equivalence X F n
        (InverseImageLocalCohomology318.comparison f F ⊤ n x) := by
  change (Ext.mk₀ (integerIso f).inv).comp
      ((((Ext.mk₀ (TerminalLocalCohomology318.generatorIso Y).inv).comp x
        (zero_add n)).mapExactFunctor (inverseImage f)).comp
          (Ext.mk₀ ((adjunction f).counit.app F)) (add_zero n)) (zero_add n) =
    (Ext.mk₀ (TerminalLocalCohomology318.generatorIso X).inv).comp
      ((Ext.mk₀ (generatorInv f ⊤)).comp
        ((x.mapExactFunctor (inverseImage f)).comp
          (Ext.mk₀ ((adjunction f).counit.app F)) (add_zero n)) (zero_add n)) (zero_add n)
  simp only [Ext.mapExactFunctor_comp,Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero,← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀]
  rw [terminal_inv_coherence]

end InverseImageTerminalCoherence318
