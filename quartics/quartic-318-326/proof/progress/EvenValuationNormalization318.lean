module
public import HeightOneContact318
public section
noncomputable section
namespace EvenValuationNormalization318
set_option maxHeartbeats 700000
open PowerSeries
open scoped TensorProduct
variable {A R:Type*} [CommRing A] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual canonical even value produces the unit and uniformizer; no
unit-times-power expression is supplied. -/
theorem even_value_decomposition (f:R) (m:ℕ)
    (hv:IsDiscreteValuationRing.addVal R f=((2*m:ℕ):ℕ∞)) :
    ∃(u:Rˣ)(pi:R), Irreducible pi ∧ f=(u:R)*pi^(2*m) := by
  have hf:f≠0 := by
    intro hz
    rw [hz,IsDiscreteValuationRing.addVal_zero] at hv
    exact ENat.top_ne_natCast (2*m) hv
  obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n,u,hu⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hpi
  have hn:n=2*m := by
    rw [IsDiscreteValuationRing.addVal_def f u hpi n hu] at hv
    exact_mod_cast hv
  subst n
  exact ⟨u,pi,hpi,hu⟩

/-- A positive even actual contact value defines formal evaluation into the
actual completed DVR, with the original contact parameter, not a chosen expression. -/
theorem formal_map (coeff:A→+*R) (f:R) (m:ℕ) (hm:0<m)
    (hv:IsDiscreteValuationRing.addVal R f=((2*m:ℕ):ℕ∞)) :
    ∃e:A⟦X⟧→+*ActualDVRCompletion318.Completion R,
      e X=algebraMap R (ActualDVRCompletion318.Completion R) f ∧
      ∀a:A,e (C a)=algebraMap R (ActualDVRCompletion318.Completion R) (coeff a) := by
  obtain ⟨u,pi,hpi,hf⟩:=even_value_decomposition f m hv
  rw [hf]
  exact ActualDVRCompletion318.completed_contact_map R coeff u pi m hpi hm

/-- The original quadratic contact algebra has an actual finite etale integral
closure and genuine generic-fiber equivalence, derived solely from its finite
even canonical valuation and invertibility of two. It may be split. -/
theorem normalization (f:R) (m:ℕ) (h2:IsUnit (2:R))
    (hv:IsDiscreteValuationRing.addVal R f=((2*m:ℕ):ℕ∞)) :
    ∃(u:Rˣ) (φ:QuadraticPresentation318.RootRing f →ₐ[R]
        (EvenContactEtale318.RootRing u ⊗[R] FractionRing R)),
      letI:Algebra (QuadraticPresentation318.RootRing f)
          (EvenContactEtale318.RootRing u ⊗[R] FractionRing R):=φ.toRingHom.toAlgebra
      IsIntegralClosure (EvenContactEtale318.RootRing u)
          (QuadraticPresentation318.RootRing f)
          (EvenContactEtale318.RootRing u ⊗[R] FractionRing R) ∧
        Algebra.Etale R (EvenContactEtale318.RootRing u) ∧
        Module.Finite R (EvenContactEtale318.RootRing u) ∧
        Function.Injective φ ∧
        Nonempty (FractionRing R ⊗[R] QuadraticPresentation318.RootRing f ≃ₐ[R]
          EvenContactEtale318.RootRing u ⊗[R] FractionRing R) := by
  obtain ⟨u,pi,hpi,hf⟩:=even_value_decomposition f m hv
  subst f
  refine ⟨u,NormalizedContactOrder318.orderToGeneric u pi m,?_⟩
  exact NormalizedContactOrder318.normalized_even_contact u pi m h2 hpi.ne_zero

end EvenValuationNormalization318
