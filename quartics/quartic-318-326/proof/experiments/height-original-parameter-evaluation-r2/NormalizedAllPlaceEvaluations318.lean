module
public import NormalizedPointEvaluationInput318
public section
noncomputable section
namespace NormalizedAllPlaceEvaluations318
open Polynomial FirstOrderCotangentEvaluation318
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type*) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]

/-- Original signed square equations and nonzero radicands derive the
nonzero-root input. The four signs themselves are not changed. -/
theorem signed_roots_nonzero (c : Fin 4 → Kˣ) (a : Fin 4 → V)
    (t : K) (y : Fin 4 → K)
    (hy : ∀ i,(y i)^2=(c i:K)*(t-algebraMap V K (a i)))
    (ht : ∀ i,t≠algebraMap V K (a i)) : ∀ i,y i≠0 := by
  intro i hz
  have h := hy i
  rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at h
  exact mul_ne_zero (c i).ne_zero (sub_ne_zero.mpr (ht i)) h.symm

/-- At every discrete finite place, the SAME original signed center yields
an actual normalized-chart cotangent functional with coordinate value 1.
Nonzero radicands remain explicit; all residue characteristics/nonunit twists
are permitted. This is not a regular-model or dualizing-lattice theorem. -/
theorem chart_evaluations (pi : V) (hp : Irreducible pi) (c : Fin 4 → Kˣ)
    (a : Fin 4 → V) (t : K) (y : Fin 4 → K)
    (hy : ∀ i,(y i)^2=(c i:K)*(t-algebraMap V K (a i)))
    (ht : ∀ i,t≠algebraMap V K (a i)) :
    ∃ (u : Fin 4 → Vˣ) (e : Fin 4 → Fin 2) (s : Fin 4 → K),
      (∀ i,s i≠0) ∧
      (∀ i,(c i:K)=algebraMap V K ((u i:V)*pi^(e i:ℕ))*(s i)^2) ∧
      ((∃ (T : V) (f : DVRNormalizedFiniteOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a →ₐ[V] V),
        algebraMap V K T=t ∧
        (∀ q : V[X],f (algebraMap V[X] (DVRNormalizedFiniteOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a) q)=Polynomial.eval T q) ∧
        (∀ i,s i*algebraMap V K (f (FourRootOrderSigns318.generator
          (DVRNormalizedFiniteOrder318.coefficient V (fun j => (u j:V)*pi^(e j:ℕ)) a) i))=y i) ∧
        (let A := DVRNormalizedFiniteOrder318.Order V (fun i => (u i:V)*pi^(e i:ℕ)) a
         letI : Algebra A V := f.toRingHom.toAlgebra
         ∃ ev : V ⊗[A] KaehlerDifferential V A →ₗ[V] K,
           ev ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (algebraMap V[X] A X))=1)) ∨
       (∃ (w : V) (f : DVRNormalizedInfinityOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a →ₐ[V] V),
        t≠0 ∧ algebraMap V K w=t⁻¹ ∧ ¬IsUnit w ∧
        (∀ q : V[X],f (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a) q)=Polynomial.eval w q) ∧
        (∀ i,s i*t*algebraMap V K (f (FourRootOrderSigns318.generator
          (DVRNormalizedInfinityOrder318.coefficient V (fun j => (u j:V)*pi^(e j:ℕ)) a) i))=y i) ∧
        (let A := DVRNormalizedInfinityOrder318.Order V (fun i => (u i:V)*pi^(e i:ℕ)) a
         letI : Algebra A V := f.toRingHom.toAlgebra
         ∃ ev : V ⊗[A] KaehlerDifferential V A →ₗ[V] K,
           ev ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (algebraMap V[X] A X))=1))) := by
  have hny := signed_roots_nonzero V K c a t y hy ht
  obtain ⟨u,e,s,hs,hc,hcharts⟩ :=
    NormalizedIntegralPointInput318.chart_center_alg V K pi hp c a t y hy
  refine ⟨u,e,s,hs,hc,?_⟩
  rcases hcharts with ⟨T,f,hT,hf,hr⟩ | ⟨w,f,ht0,hw,hwn,hf,hr⟩
  · exact Or.inl ⟨T,f,hT,hf,hr,
      NormalizedPointEvaluationInput318.finite_evaluation V K _ a s y T t f hT hf hr hny⟩
  · exact Or.inr ⟨w,f,ht0,hw,hwn,hf,hr,
      NormalizedPointEvaluationInput318.infinity_evaluation V K _ a s y w t f hw hf hr hny⟩
end NormalizedAllPlaceEvaluations318
