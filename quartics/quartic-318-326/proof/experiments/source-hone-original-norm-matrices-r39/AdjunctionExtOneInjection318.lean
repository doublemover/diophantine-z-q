module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

public section
noncomputable section
namespace AdjunctionExtOneInjection318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
universe w₁ w₂
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{w₁} C] [HasExt.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]
  (adj : L ⊣ R)

@[expose] def mate (A : C) (B : D) (n : ℕ) : Ext A (R.obj B) n →+ Ext (L.obj A) B n :=
  ((Ext.mk₀ (adj.counit.app B)).postcomp (L.obj A) (add_zero n)).comp
    (L.mapExtAddHom A (R.obj B) n)

omit [R.Additive] [PreservesFiniteLimits R] in
theorem mate_apply (A : C) (B : D) (n : ℕ) (x : Ext A (R.obj B) n) :
    mate adj A B n x = (x.mapExactFunctor L).comp
      (Ext.mk₀ (adj.counit.app B)) (add_zero n) := rfl

/-- The adjunction mate on Ext¹ is injective even when the right adjoint is not exact. -/
theorem mate_one_injective [EnoughInjectives D] (A : C) (B : D) :
    Function.Injective (mate adj A B 1) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  change mate adj A B 1 x = 0 at hx
  let i := Injective.ι B
  let S : ShortComplex D := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
  let T : ShortComplex C := ShortComplex.mk (R.map i) (cokernel.π (R.map i))
    (cokernel.condition (R.map i))
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (R.map i)) }
  have hRI : Injective (R.obj (Injective.under B)) := adj.map_injective _ inferInstance
  obtain ⟨u₀, hu₀⟩ := Ext.covariant_sequence_exact₁ A hT x
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨u, rfl⟩ := (Ext.mk₀_bijective _ _).surjective u₀
  let j : T.X₃ ⟶ R.obj S.X₃ := cokernel.desc (R.map i) (R.map S.g)
    (by rw [← R.map_comp, S.zero, R.map_zero])
  have hj : Mono j :=
    (hS.exact.map_of_mono_of_preservesKernel R inferInstance inferInstance).mono_cokernelDesc
  let β : L.obj T.X₃ ⟶ S.X₃ := (adj.homEquiv _ _).symm j
  have hβ : L.map T.g ≫ β = adj.counit.app (Injective.under B) ≫ S.g := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    dsimp [β, j, T]
    rw [← adj.homEquiv_symm_id]
    simp
  let φ : T.map L ⟶ S :=
    { τ₁ := adj.counit.app B
      τ₂ := adj.counit.app (Injective.under B)
      τ₃ := β
      comm₁₂ := (adj.counit.naturality i).symm
      comm₂₃ := hβ.symm }
  have hδ : (hT.extClass.mapExactFunctor L).comp
      (Ext.mk₀ (adj.counit.app B)) (add_zero 1) =
      (Ext.mk₀ β).comp hS.extClass (zero_add 1) := by
    rw [Ext.mapExactFunctor_extClass]
    exact ShortComplex.ShortExact.extClass_naturality (hT.map L) hS φ
  have hz : (Ext.mk₀ (L.map u ≫ β)).comp hS.extClass (zero_add 1) = 0 := by
    rw [← hu₀] at hx
    simp only [mate_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc_of_third_deg_zero, hδ] at hx
    simpa only [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] using hx
  obtain ⟨v₀, hv₀⟩ := Ext.covariant_sequence_exact₃ (L.obj A) hS
    (Ext.mk₀ (L.map u ≫ β)) (n₁ := 1) rfl hz
  obtain ⟨v, rfl⟩ := (Ext.mk₀_bijective _ _).surjective v₀
  have hv : v ≫ S.g = L.map u ≫ β := by
    apply (Ext.mk₀_bijective _ _).injective
    simpa only [Ext.mk₀_comp_mk₀] using hv₀
  have hu : (adj.homEquiv _ _ v) ≫ T.g = u := by
    apply (cancel_mono j).mp
    rw [Category.assoc]
    change _ ≫ (cokernel.π (R.map i) ≫ cokernel.desc (R.map i) (R.map S.g) _) = _
    rw [cokernel.π_desc]
    have hh := congrArg (adj.homEquiv _ _) hv
    simpa only [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
      Equiv.apply_symm_apply, β] using hh
  rw [← hu₀, ← hu, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
  rw [hT.comp_extClass, Ext.comp_zero]

end AdjunctionExtOneInjection318
