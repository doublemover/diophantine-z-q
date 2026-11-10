module
public import AdjunctionExtOneInjection318

public section
noncomputable section
namespace AdjunctionExtOneSurjection318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AdjunctionExtOneInjection318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
universe w₁ w₂
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{w₁} C] [HasExt.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]
  (adj : L ⊣ R)

/-- Surjectivity of the actual Ext¹ mate needs exactness of only the chosen
injective-cokernel sequence after the right adjoint, not exactness of the whole functor. -/
theorem mate_one_surjective [EnoughInjectives D] (A : C) (B : D)
    (hepi : Epi (R.map (cokernel.π (Injective.ι B)))) :
    Function.Surjective (mate adj A B 1) := by
  let i := Injective.ι B
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
  have hm : Mono S.f := hS.mono_f
  have hT : (S.map R).ShortExact :=
    { exact := hS.exact.map_of_mono_of_preservesKernel R inferInstance inferInstance
      mono_f := (show Mono (R.map S.f) from inferInstance)
      epi_g := hepi }
  have htm : Mono (S.map R).f := hT.mono_f
  have hte : Epi (S.map R).g := hT.epi_g
  intro x
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ (L.obj A) hS x
    (Ext.eq_zero_of_injective _) (n₀:=0) rfl
  obtain ⟨u,rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  let v := adj.homEquiv A S.X₃ u
  let φ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app B
      τ₂ := adj.counit.app (Injective.under B)
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  have hδ : (hT.extClass.mapExactFunctor L).comp
      (Ext.mk₀ (adj.counit.app B)) (add_zero 1) =
      (Ext.mk₀ (adj.counit.app S.X₃)).comp hS.extClass (zero_add 1) := by
    rw [Ext.mapExactFunctor_extClass]
    exact ShortComplex.ShortExact.extClass_naturality (hT.map L) hS φ
  refine ⟨(Ext.mk₀ v).comp hT.extClass (zero_add 1),?_⟩
  rw [mate_apply,Ext.mapExactFunctor_comp,Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero,hδ,← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  have hv : L.map v ≫ adj.counit.app S.X₃ = u :=
    (adj.homEquiv A S.X₃).symm_apply_apply u
  rw [hv]
  exact hy

end AdjunctionExtOneSurjection318
