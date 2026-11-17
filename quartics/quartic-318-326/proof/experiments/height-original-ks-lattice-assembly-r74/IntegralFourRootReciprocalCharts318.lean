module
public import IntegralScaledFourRootModel318
public section
noncomputable section
namespace IntegralFourRootReciprocalCharts318
open Polynomial
variable {R : Type*} [CommRing R] (d a : Fin 4 → R)

/-- Full finite chart, permitting nonunit or zero coefficient images. -/
@[expose] def finiteCoefficient (i : Fin 4) : R[X] := C (d i) * (X - C (a i))
/-- Reciprocal chart obtained by z_i=s*y_i. This quadratic-in-s equation
retains all special-fiber points; no root or coefficient is inverted. -/
@[expose] def reciprocalCoefficient (i : Fin 4) : R[X] :=
  C (d i) * X * (1 - C (a i) * X)
abbrev FiniteOrder := FourRootOrder318.Order (finiteCoefficient d a)
abbrev ReciprocalOrder := FourRootOrder318.Order (reciprocalCoefficient d a)

theorem finite_chart_free : Module.Finite R[X] (FiniteOrder d a) ∧
    Module.Free R[X] (FiniteOrder d a) := FourRootOrder318.finite_free _
theorem reciprocal_chart_free : Module.Finite R[X] (ReciprocalOrder d a) ∧
    Module.Free R[X] (ReciprocalOrder d a) := FourRootOrder318.finite_free _

variable {S : Type*} [CommRing S] [Algebra R S] (s : Sˣ)

/-- Exact coordinate calculation on the overlap: t=s⁻¹ and z_i=s*y_i.
The only unit here is the base-chart coordinate s, never a twist or prime. -/
theorem overlap_coefficient (i : Fin 4) :
    Polynomial.aeval (s : S) (reciprocalCoefficient d a i) =
      Polynomial.aeval ((s⁻¹ : Sˣ) : S) (finiteCoefficient d a i) * (s : S)^2 := by
  simp only [reciprocalCoefficient, finiteCoefficient, map_mul, map_sub, map_one,
    Polynomial.aeval_C, Polynomial.aeval_X]
  have hs : ((s⁻¹ : Sˣ) : S) * (s : S) = 1 := s.inv_mul
  calc
    algebraMap R S (d i) * (s : S) * (1 - algebraMap R S (a i) * (s : S)) =
      algebraMap R S (d i) *
        (((s⁻¹ : Sˣ) : S) * (s : S) - algebraMap R S (a i) * (s : S)) * (s : S) := by rw [hs]; ring
    _ = (algebraMap R S (d i) * (((s⁻¹ : Sˣ) : S) - algebraMap R S (a i))) *
        (s : S)^2 := by ring

/-- A constructed four-root algebra equivalence on the actual reciprocal
coordinate overlap. This is the algebraic transition needed for gluing,
not a claim that a proper or normal scheme has already been assembled. -/
@[expose] def overlapEquiv :
    FourRootOrder318.Order (fun i => Polynomial.aeval (s : S) (reciprocalCoefficient d a i)) ≃ₐ[S]
      FourRootOrder318.Order (fun i => Polynomial.aeval ((s⁻¹ : Sˣ) : S) (finiteCoefficient d a i)) :=
  IntegralScaledFourRootModel318.fourScale _ _ (fun _ => s) (overlap_coefficient d a s)

end IntegralFourRootReciprocalCharts318
