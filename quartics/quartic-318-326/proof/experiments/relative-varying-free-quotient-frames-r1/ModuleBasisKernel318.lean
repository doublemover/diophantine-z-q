module
public import ActualClosedIdealModule318
public import ModuleFrameDescent318
public section
noncomputable section
namespace ModuleBasisKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
  {ι : Type u} (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
  (he : ∀ i,LinearMap.range (f.val.app (op (B i))).hom=LinearMap.ker (g.val.app (op (B i))).hom)

/-- Exact section kernels on an actual basis force the original global
composite to vanish, by the actual sheaf separation theorem. -/
lemma composite_zero : f ≫ g=0 := by
  have hh : (f ≫ g).mapPresheaf=(0 : M ⟶ P).mapPresheaf := by
    apply TopCat.Sheaf.hom_ext _ ⟨P.presheaf,P.isSheaf⟩ hB
    intro i
    ext a
    have hm : f.app (B i) a ∈ LinearMap.range (f.val.app (op (B i))).hom := ⟨a,rfl⟩
    rw [he i] at hm
    exact hm
  apply Scheme.Modules.hom_ext
  intro V
  ext a
  exact congrArg (fun k => k.app (op V) a) hh

/-- The canonical factor retains the actual global morphism f. -/
@[expose] def factor : M ⟶ kernel g := kernel.lift g f (composite_zero f g B hB he)
@[reassoc] lemma factor_inclusion : factor f g B hB he ≫ kernel.ι g=f :=
  kernel.lift_ι _ _ _
lemma factor_value (V : X.Opens) (a : Γ(M,V)) :
    (kernel.ι g).app V ((factor f g B hB he).app V a)=f.app V a :=
  congrArg (fun k => k.app V a) (factor_inclusion f g B hB he)

lemma inclusion_injective (V : X.Opens) : Function.Injective ((kernel.ι g).app V) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op V)
  haveI : Mono (E.map (kernel.ι g)) := inferInstance
  exact (ModuleCat.mono_iff_injective (E.map (kernel.ι g))).mp inferInstance

lemma factor_surjective (i : ι) : Function.Surjective ((factor f g B hB he).app (B i)) := by
  intro a
  have hz : g.app (B i) ((kernel.ι g).app (B i) a)=0 :=
    congrArg (fun k => k.app (B i) a) (kernel.condition g)
  have hm : (kernel.ι g).app (B i) a ∈ LinearMap.range (f.val.app (op (B i))).hom := by
    rw [he i]
    exact hz
  obtain ⟨b,hb⟩ := hm
  refine ⟨b,?_⟩
  apply inclusion_injective g (B i)
  rw [factor_value]
  exact hb

variable (hi : ∀ i,Function.Injective (f.app (B i)))
lemma factor_bijective (i : ι) : Function.Bijective ((factor f g B hB he).app (B i)) := by
  refine ⟨?_,factor_surjective f g B hB he i⟩
  intro a b hab
  apply hi i
  have h := congrArg (fun t => (kernel.ι g).app (B i) t) hab
  simpa only [factor_value] using h

/-- Basis-only exactness and injectivity suffice: there is no need to
postulate principal kernel equations on every non-affine open. This is
particularly important for the actual affine quotient-chart producer. -/
lemma factor_isIso : IsIso (factor f g B hB he) := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hf : IsIso (F.map (factor f g B hB he)) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B:=B) hB
    intro i
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact factor_bijective f g B hB he hi i
  letI := hf
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  exact (inferInstance : IsIso ((F.map (factor f g B hB he)).hom.app (op V)))

@[expose] def iso : M ≅ kernel g := by
  letI := factor_isIso f g B hB he hi
  exact asIso (factor f g B hB he)
@[reassoc] lemma iso_hom_inclusion : (iso f g B hB he hi).hom ≫ kernel.ι g=f :=
  factor_inclusion f g B hB he
end ModuleBasisKernel318
