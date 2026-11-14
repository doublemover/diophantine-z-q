module
public import ActualLinearRootDifferent318
public section
noncomputable section
namespace ActualLinearRootPrime318
open Polynomial LinearRootCoordinate318 ActualLinearRootDifferent318
variable (a:ℂ)
@[expose] def prime:Ideal (B a):=RingHom.ker (branchEvaluation (1:ℂˣ) a).toRingHom
lemma maximal:(prime a).IsMaximal:=by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨algebraMap ℂ (B a) c,(branchEvaluation (1:ℂˣ) a).commutes c⟩
lemma prime_eq:prime a=Ideal.span {root a}:=by
  ext x
  rw [Ideal.mem_span_singleton]
  change branchEvaluation (1:ℂˣ) a x=0↔root a∣x
  constructor
  · intro hx
    have hp:Polynomial.IsRoot (coordinateEquiv (1:ℂˣ) a x) 0:=hx
    have hd:(X:ℂ[X])∣coordinateEquiv (1:ℂˣ) a x:=by
      simpa only [map_zero,sub_zero] using Polynomial.dvd_iff_isRoot.mpr hp
    obtain ⟨q,hq⟩:=hd
    refine ⟨(coordinateEquiv (1:ℂˣ) a).symm q,?_⟩
    apply (coordinateEquiv (1:ℂˣ) a).injective
    rw [map_mul,AlgEquiv.apply_symm_apply]
    change _=X*q
    exact hq
  · rintro ⟨q,rfl⟩
    rw [map_mul]
    simp only [root,LinearRootCoordinate318.branchEvaluation_root,zero_mul]
lemma root_ne_zero:root a≠0:=by
  intro hz
  have h:=congrArg (coordinateEquiv (1:ℂˣ) a) hz
  change (X:ℂ[X])=coordinateEquiv (1:ℂˣ) a 0 at h
  rw [map_zero] at h
  exact Polynomial.X_ne_zero h
lemma prime_ne_bot:prime a≠⊥:=by
  rw [prime_eq]
  intro h
  have hr:root a∈Ideal.span {root a}:=Ideal.subset_span (Set.mem_singleton _)
  rw [h,Ideal.mem_bot] at hr
  exact root_ne_zero a hr
end ActualLinearRootPrime318
