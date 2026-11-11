module
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Quotient.Defs
public section
noncomputable section
namespace TwoChartFiniteRelations318
set_option maxHeartbeats 750000
universe u v w
variable {R : Type u} [CommRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {M : Type w} [AddCommGroup M] [Module R M]
  (f : E →ₗ[R] M) (P Q : Submodule R E)

@[expose] def sourceBoundary : Submodule R E := P ⊔ Q
@[expose] def targetBoundary : Submodule R M := P.map f ⊔ Q.map f

lemma image_boundary (x : E) (hx : x ∈ sourceBoundary P Q) :
    f x ∈ targetBoundary f P Q := by
  obtain ⟨p,hp,q,hq,rfl⟩ := Submodule.mem_sup.mp hx
  exact Submodule.mem_sup.mpr ⟨f p,⟨p,hp,rfl⟩,f q,⟨q,hq,rfl⟩,by rw [map_add]⟩

@[expose] def quotientMap : (E ⧸ sourceBoundary P Q) →ₗ[R] (M ⧸ targetBoundary f P Q) :=
  (sourceBoundary P Q).liftQ ((targetBoundary f P Q).mkQ.comp f) (by
    intro x hx
    change (targetBoundary f P Q).mkQ (f x) = 0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact image_boundary f P Q x hx)

lemma quotientMap_mk (x : E) :
    quotientMap f P Q ((sourceBoundary P Q).mkQ x) = (targetBoundary f P Q).mkQ (f x) := rfl

lemma quotientMap_surjective (hf : Function.Surjective f) : Function.Surjective (quotientMap f P Q) := by
  intro z
  obtain ⟨m,rfl⟩ := (targetBoundary f P Q).mkQ_surjective z
  obtain ⟨e,rfl⟩ := hf m
  exact ⟨(sourceBoundary P Q).mkQ e,rfl⟩

@[expose] def kernelBoundary : Submodule R (LinearMap.ker f) :=
  P.comap (LinearMap.ker f).subtype ⊔ Q.comap (LinearMap.ker f).subtype

@[expose] def kernelInto : LinearMap.ker f →ₗ[R] LinearMap.ker (quotientMap f P Q) :=
  ((sourceBoundary P Q).mkQ.comp (LinearMap.ker f).subtype).codRestrict
    (LinearMap.ker (quotientMap f P Q)) (by
      intro x
      change (targetBoundary f P Q).mkQ (f x) = 0
      rw [x.property,map_zero])

lemma kernelBoundary_zero (x : LinearMap.ker f) (hx : x ∈ kernelBoundary f P Q) :
    kernelInto f P Q x = 0 := by
  apply Subtype.ext
  change (sourceBoundary P Q).mkQ (x : E) = 0
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
  exact Submodule.mem_sup.mpr ⟨a,ha,b,hb,rfl⟩

/-- Genuine Cech relation classes map to the kernel of the original
quotient map; no H1 exactness or finite-relation premise is assumed. -/
@[expose] def relationMap : ((LinearMap.ker f) ⧸ kernelBoundary f P Q) →ₗ[R]
    LinearMap.ker (quotientMap f P Q) :=
  (kernelBoundary f P Q).liftQ (kernelInto f P Q)
    (fun x hx => kernelBoundary_zero f P Q x hx)

/-- Every relation downstairs lifts to an actual overlap relation after
subtracting its two original chart representatives. -/
lemma relationMap_surjective : Function.Surjective (relationMap f P Q) := by
  intro z
  obtain ⟨e,he⟩ := (sourceBoundary P Q).mkQ_surjective (z : E ⧸ sourceBoundary P Q)
  have hz : f e ∈ targetBoundary f P Q := by
    have h := z.property
    rw [← he,quotientMap_mk] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  obtain ⟨p,⟨a,ha,hap⟩,q,⟨b,hb,hbq⟩,hpq⟩ := Submodule.mem_sup.mp hz
  have hk : f (e-(a+b)) = 0 := by
    rw [map_sub,map_add,hap,hbq,hpq,sub_self]
  let k : LinearMap.ker f := ⟨e-(a+b),hk⟩
  refine ⟨(kernelBoundary f P Q).mkQ k,?_⟩
  apply Subtype.ext
  change (sourceBoundary P Q).mkQ (e-(a+b)) = z
  have hab : (sourceBoundary P Q).mkQ (a+b) = 0 := by
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup.mpr ⟨a,ha,b,hb,rfl⟩
  rw [map_sub,hab,sub_zero,he]

/-- Finite chart-relation cohomology supplies a FINITELY GENERATED kernel
for the actual H1 quotient presentation. This implication is valid over
arbitrary commutative rings; no Noetherian/coherence assumption is used. -/
lemma quotient_kernel_finite
    [Module.Finite R ((LinearMap.ker f) ⧸ kernelBoundary f P Q)] :
    Module.Finite R (LinearMap.ker (quotientMap f P Q)) :=
  Module.Finite.of_surjective (relationMap f P Q) (relationMap_surjective f P Q)

/-- Exact finite-presentation criterion for the original two-chart
quotient, retaining the actual free-source and kernel-Cech modules. -/
theorem finitePresentation (hf : Function.Surjective f)
    [Module.FinitePresentation R (E ⧸ sourceBoundary P Q)]
    [Module.Finite R ((LinearMap.ker f) ⧸ kernelBoundary f P Q)] :
    Module.FinitePresentation R (M ⧸ targetBoundary f P Q) := by
  letI := quotient_kernel_finite f P Q
  have hfg : (LinearMap.ker (quotientMap f P Q)).FG := by
    have h := (Module.Finite.fg_top (R := R) (M := LinearMap.ker (quotientMap f P Q))).map
      (LinearMap.ker (quotientMap f P Q)).subtype
    simpa only [Submodule.map_top,Submodule.range_subtype] using h
  exact Module.finitePresentation_of_surjective (quotientMap f P Q)
    (quotientMap_surjective f P Q hf) hfg
end TwoChartFiniteRelations318
