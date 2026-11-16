module
public import NormalizedIntegralPointInput318
public import NormalizedCotangentEvaluation318
public section
noncomputable section
namespace NormalizedPointEvaluationInput318
open Polynomial FirstOrderCotangentEvaluation318
open scoped TensorProduct
variable (V K : Type*) [CommRing V] [Field K] [CharZero K] [Algebra V K]

/-- Derive the complete field-polynomial identity from the SAME integral
point and its already constructed evaluation coordinate. -/
theorem field_polynomial {A : Type*} [CommRing A] [Algebra V A]
    [Algebra V[X] A] (f : A →ₐ[V] V) (T : V) (t : K)
    (hT : algebraMap V K T=t)
    (hf : ∀ q : V[X],f (algebraMap V[X] A q)=Polynomial.eval T q)
    (q : V[X]) :
    fieldPoint V A K f (algebraMap V[X] A q)=Polynomial.aeval t q := by
  change algebraMap V K (f (algebraMap V[X] A q))=Polynomial.aeval t q
  rw [hf q,← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,hT]

/-- Original nonzero signed roots force all actual finite-chart generator
values to be nonzero; this is not an extra assumption about the model. -/
theorem finite_roots_nonzero (d a : Fin 4 → V) (s y : Fin 4 → K)
    (f : DVRNormalizedFiniteOrder318.Order V d a →ₐ[V] V)
    (hr : ∀ i,s i*algebraMap V K (f (FourRootOrderSigns318.generator
      (DVRNormalizedFiniteOrder318.coefficient V d a) i))=y i)
    (hy : ∀ i,y i≠0) :
    ∀ i,fieldPoint V (DVRNormalizedFiniteOrder318.Order V d a) K f
      (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient V d a) i)≠0 := by
  intro i hz
  apply hy i
  have h := hr i
  change s i*fieldPoint V (DVRNormalizedFiniteOrder318.Order V d a) K f
    (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient V d a) i)=y i at h
  rw [hz,mul_zero] at h
  exact h.symm

/-- The reciprocal signed relation retains its original extra t factor.
No inversion of t, s, 2, or the twists in the integral ring is used here. -/
theorem infinity_roots_nonzero (d a : Fin 4 → V) (s y : Fin 4 → K) (t : K)
    (f : DVRNormalizedInfinityOrder318.Order V d a →ₐ[V] V)
    (hr : ∀ i,s i*t*algebraMap V K (f (FourRootOrderSigns318.generator
      (DVRNormalizedInfinityOrder318.coefficient V d a) i))=y i)
    (hy : ∀ i,y i≠0) :
    ∀ i,fieldPoint V (DVRNormalizedInfinityOrder318.Order V d a) K f
      (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient V d a) i)≠0 := by
  intro i hz
  apply hy i
  have h := hr i
  change s i*t*fieldPoint V (DVRNormalizedInfinityOrder318.Order V d a) K f
    (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient V d a) i)=y i at h
  rw [hz,mul_zero] at h
  exact h.symm

/-- Supply the actual finite-chart cotangent functional from the original
signed integral center, without caller-supplied derivative or field identities. -/
theorem finite_evaluation (d a : Fin 4 → V) (s y : Fin 4 → K) (T : V) (t : K)
    (f : DVRNormalizedFiniteOrder318.Order V d a →ₐ[V] V)
    (hT : algebraMap V K T=t)
    (hf : ∀ q : V[X],f (algebraMap V[X] (DVRNormalizedFiniteOrder318.Order V d a) q)=Polynomial.eval T q)
    (hr : ∀ i,s i*algebraMap V K (f (FourRootOrderSigns318.generator
      (DVRNormalizedFiniteOrder318.coefficient V d a) i))=y i)
    (hy : ∀ i,y i≠0) :
    let A := DVRNormalizedFiniteOrder318.Order V d a
    letI : Algebra A V := f.toRingHom.toAlgebra
    ∃ ev : V ⊗[A] KaehlerDifferential V A →ₗ[V] K,
      ev ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (algebraMap V[X] A X))=1 := by
  let hfK := field_polynomial V K f T t hT hf
  let hn := finite_roots_nonzero V K d a s y f hr hy
  exact ⟨NormalizedCotangentEvaluation318.finiteEvaluation V K d a t f hfK hn,
    NormalizedCotangentEvaluation318.finiteEvaluation_dX V K d a t f hfK hn⟩

/-- Analogous actual reciprocal functional. Its normalization is Dw=1,
not Dt=1; conversion to the original rational frame is still separate. -/
theorem infinity_evaluation (d a : Fin 4 → V) (s y : Fin 4 → K) (w : V) (t : K)
    (f : DVRNormalizedInfinityOrder318.Order V d a →ₐ[V] V)
    (hw : algebraMap V K w=t⁻¹)
    (hf : ∀ q : V[X],f (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V d a) q)=Polynomial.eval w q)
    (hr : ∀ i,s i*t*algebraMap V K (f (FourRootOrderSigns318.generator
      (DVRNormalizedInfinityOrder318.coefficient V d a) i))=y i)
    (hy : ∀ i,y i≠0) :
    let A := DVRNormalizedInfinityOrder318.Order V d a
    letI : Algebra A V := f.toRingHom.toAlgebra
    ∃ ev : V ⊗[A] KaehlerDifferential V A →ₗ[V] K,
      ev ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (algebraMap V[X] A X))=1 := by
  let hfK := field_polynomial V K f w t⁻¹ hw hf
  let hn := infinity_roots_nonzero V K d a s y t f hr hy
  exact ⟨NormalizedCotangentEvaluation318.infinityEvaluation V K d a t⁻¹ f hfK hn,
    NormalizedCotangentEvaluation318.infinityEvaluation_dX V K d a t⁻¹ f hfK hn⟩
end NormalizedPointEvaluationInput318
