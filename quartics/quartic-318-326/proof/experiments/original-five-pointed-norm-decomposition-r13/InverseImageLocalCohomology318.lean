module
public import InverseImageLocalGenerator318
public import LocalSheafCohomologyAdditive318
public import SourceCohomologyComparison318

public section
noncomputable section
namespace InverseImageLocalCohomology318
open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 LocalSheafCohomologyAdditive318
open SheafInverseImageConstants318 InverseImageLocalGenerator318
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : ASheaf (X:=X))

/-- The original inverse-image Ext comparison at an arbitrary open, with its canonical generator. -/
@[expose] def comparison (U : Opens Y) (n : ℕ) :
    ((directImage f).obj F).H' n U →+ F.H' n ((Opens.map f).obj U) :=
  ((Ext.mk₀ (generatorInv f U)).precomp F (zero_add n)).comp
    (((Ext.mk₀ ((adjunction f).counit.app F)).postcomp
      ((inverseImage f).obj (generator U)) (add_zero n)).comp
      ((inverseImage f).mapExtAddHom _ _ n))

theorem comparison_apply (U : Opens Y) (n : ℕ)
    (x : ((directImage f).obj F).H' n U) :
    comparison f F U n x = (Ext.mk₀ (generatorInv f U)).comp
      ((x.mapExactFunctor (inverseImage f)).comp
        (Ext.mk₀ ((adjunction f).counit.app F)) (add_zero n)) (zero_add n) := rfl

/-- Its degree-zero map is literally the original adjunction, not a freely chosen equivalence. -/
theorem comparison_mkZero (U : Opens Y) (a : generator U ⟶ (directImage f).obj F) :
    comparison f F U 0 (Ext.mk₀ a) =
      Ext.mk₀ (generatorInv f U ≫ ((adjunction f).homEquiv _ _).symm a) := by
  simp only [comparison_apply,Ext.mapExactFunctor_mk₀,Ext.mk₀_comp_mk₀]
  rfl

/-- Direct-image local sections and actual source sections coincide under this derived comparison. -/
theorem comparison_zero_sections (U : Opens Y) (x : ((directImage f).obj F).H' 0 U) :
    zeroAddEquiv F ((Opens.map f).obj U) (comparison f F U 0 x) =
      zeroAddEquiv ((directImage f).obj F) U x := by
  obtain ⟨a,rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  rw [comparison_mkZero]
  change sectionEquiv F ((Opens.map f).obj U)
      (Ext.homEquiv₀ (Ext.mk₀ (generatorInv f U ≫ ((adjunction f).homEquiv _ _).symm a))) =
    sectionEquiv ((directImage f).obj F) U (Ext.homEquiv₀ (Ext.mk₀ a))
  rw [Ext.homEquiv₀.apply_symm_apply,Ext.homEquiv₀.apply_symm_apply]
  rw [generatorInv_section]
  exact congrArg (sectionEquiv ((directImage f).obj F) U)
    (((adjunction f).homEquiv _ _).apply_symm_apply a)

/-- Naturality in coefficient sheaves retains the original adjunction counit. -/
theorem comparison_coefficients {F G : ASheaf (X:=X)} (a : F ⟶ G)
    (U : Opens Y) (n : ℕ) (x : ((directImage f).obj F).H' n U) :
    comparison f G U n (x.comp (Ext.mk₀ ((directImage f).map a)) (add_zero n)) =
      (comparison f F U n x).comp (Ext.mk₀ a) (add_zero n) := by
  simp only [comparison_apply,Ext.mapExactFunctor_comp,Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc _ _ _ _ (add_zero 0) (by omega),Ext.mk₀_comp_mk₀]
  rw [(adjunction f).counit.naturality a,← Ext.mk₀_comp_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero]

/-- Naturality in every open restriction, with the actual inverse-image arrow. -/
theorem comparison_restriction {U V : Opens Y} (i : U ⟶ V) (n : ℕ)
    (x : ((directImage f).obj F).H' n V) :
    comparison f F U n ((((directImage f).obj F).cohomologyPresheaf n).map i.op x) =
      (F.cohomologyPresheaf n).map ((Opens.map f).map i).op (comparison f F V n x) := by
  change comparison f F U n
      ((Ext.mk₀ (LocalCohomologyRestriction318.generatorMap i)).comp x (zero_add n)) =
    (Ext.mk₀ (LocalCohomologyRestriction318.generatorMap ((Opens.map f).map i))).comp
      (comparison f F V n x) (zero_add n)
  simp only [comparison_apply,Ext.mapExactFunctor_comp,Ext.mapExactFunctor_mk₀]
  simp only [← Ext.comp_assoc_of_second_deg_zero,Ext.comp_assoc_of_third_deg_zero]
  rw [Ext.mk₀_comp_mk₀,Ext.mk₀_comp_mk₀,generatorInv_naturality]

end InverseImageLocalCohomology318
