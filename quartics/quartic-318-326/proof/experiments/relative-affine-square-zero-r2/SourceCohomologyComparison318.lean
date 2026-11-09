module
public import SheafInverseImageConstants318
public import AdjunctionExtOneInjection318

public section
noncomputable section
namespace SourceCohomologyComparison318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open SheafInverseImageConstants318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : TopCat.{0}} (f : X ⟶ Y)
variable (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})

/-- The canonical derived comparison, obtained by exact inverse image, the original
adjunction counit, and preservation of the original constant integer sheaf. -/
@[expose] def comparison (n : ℕ) : Sheaf.H ((directImage f).obj F) n →+ Sheaf.H F n :=
  ((Ext.mk₀ (integerIso f).inv).precomp F (zero_add n)).comp
    (((Ext.mk₀ ((adjunction f).counit.app F)).postcomp
      ((inverseImage f).obj (integerSheaf Y)) (add_zero n)).comp
      ((inverseImage f).mapExtAddHom _ _ n))

theorem comparison_apply (n : ℕ) (x : Sheaf.H ((directImage f).obj F) n) :
    comparison f F n x = (Ext.mk₀ (integerIso f).inv).comp
      ((x.mapExactFunctor (inverseImage f)).comp
        (Ext.mk₀ ((adjunction f).counit.app F)) (add_zero n)) (zero_add n) := rfl

/-- In degree zero this is exactly the inverse adjunction on the represented morphism. -/
theorem comparison_mkZero (x : integerSheaf Y ⟶ (directImage f).obj F) :
    comparison f F 0 (Ext.mk₀ x) =
      Ext.mk₀ ((integerIso f).inv ≫ ((adjunction f).homEquiv _ _).symm x) := by
  simp only [comparison_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  rfl

/-- The comparison is natural in the actual source coefficient sheaf. -/
theorem comparison_naturality {F G : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{0}} (a : F ⟶ G)
    (n : ℕ) (x : Sheaf.H ((directImage f).obj F) n) :
    comparison f G n (Sheaf.H.map ((directImage f).map a) n x) =
      Sheaf.H.map a n (comparison f F n x) := by
  simp only [comparison_apply, Sheaf.H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc _ _ _ _ (add_zero 0) (by omega), Ext.mk₀_comp_mk₀]
  have hn : (inverseImage f).map ((directImage f).map a) ≫ (adjunction f).counit.app G =
      (adjunction f).counit.app F ≫ a := (adjunction f).counit.naturality a
  rw [hn]
  rw [← Ext.mk₀_comp_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero]

/-- Degree zero is an isomorphism without any exactness hypothesis on direct image. -/
theorem comparison_zero_bijective : Function.Bijective (comparison f F 0) := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    rw [comparison_mkZero, comparison_mkZero] at h
    have h' := (Ext.mk₀_bijective _ _).injective h
    have h'' := (cancel_epi (integerIso f).inv).mp h'
    exact congrArg Ext.mk₀ (((adjunction f).homEquiv _ _).symm.injective h'')
  · intro x
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    refine ⟨Ext.mk₀ ((adjunction f).homEquiv _ _ ((integerIso f).hom ≫ a)), ?_⟩
    rw [comparison_mkZero, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]

/-- The genuine comparison to source cohomology is injective in degree one.
This uses left exactness of direct image, not the false blanket assumption that it is exact. -/
theorem comparison_one_injective : Function.Injective (comparison f F 1) := by
  have hi : Function.Injective ((Ext.mk₀ (integerIso f).inv).precomp F (zero_add 1)) := by
    intro a b h
    have hh := congrArg (fun z => (Ext.mk₀ (integerIso f).hom).comp z (zero_add 1)) h
    change (Ext.mk₀ (integerIso f).hom).comp
      ((Ext.mk₀ (integerIso f).inv).comp a (zero_add 1)) (zero_add 1) =
      (Ext.mk₀ (integerIso f).hom).comp
      ((Ext.mk₀ (integerIso f).inv).comp b (zero_add 1)) (zero_add 1) at hh
    simpa only [← Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.mk₀_id_comp] using hh
  exact hi.comp (AdjunctionExtOneInjection318.mate_one_injective
    (adjunction f) (integerSheaf Y) F)

end SourceCohomologyComparison318
