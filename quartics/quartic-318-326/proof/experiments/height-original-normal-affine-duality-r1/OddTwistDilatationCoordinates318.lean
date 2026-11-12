module
public import DVRNormalizedFiniteOrder318
public import IntegralRootPointMaps318
public section
noncomputable section
namespace OddTwistDilatationCoordinates318
open Polynomial
set_option maxHeartbeats 1000000
variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/-- A genuine odd normalized twist forces the SPECIFIED integral root
to be divisible by the same uniformizer. Cancelling it gives an integral
new coordinate, not a fraction-field choice or an assumed regular model. -/
theorem exists_coordinate (pi : V) (hp : Irreducible pi) (u : Vˣ)
    (a T y : V) (hy : y^2 = (u : V)*pi*(T-a)) :
    ∃ z : V, y=pi*z ∧ T=a+pi*(↑u⁻¹ : V)*z^2 := by
  have hd : pi ∣ y^2 := ⟨(u : V)*(T-a), by rw [hy]; ring⟩
  obtain ⟨z,hz⟩ := hp.prime.dvd_of_dvd_pow hd
  refine ⟨z,hz,?_⟩
  have hc : pi*z^2 = (u : V)*(T-a) := by
    apply mul_left_cancel₀ hp.ne_zero
    calc
      pi*(pi*z^2) = (pi*z)^2 := by ring
      _ = (u : V)*pi*(T-a) := by rw [←hz,hy]
      _ = pi*((u : V)*(T-a)) := by ring
  have hu : (↑u⁻¹ : V)*pi*z^2 = T-a := by
    calc
      _ = (↑u⁻¹ : V)*(pi*z^2) := by ring
      _ = (↑u⁻¹ : V)*((u : V)*(T-a)) := congrArg (fun q : V => (↑u⁻¹ : V)*q) hc
      _ = T-a := by rw [←mul_assoc,Units.inv_mul,one_mul]
  linear_combination -hu

theorem contact_difference_dvd (pi : V) (hp : Irreducible pi) (u : Vˣ)
    (a T y : V) (hy : y^2=(u : V)*pi*(T-a)) : pi ∣ T-a := by
  obtain ⟨z,hz,hT⟩ := exists_coordinate pi hp u a T y hy
  refine ⟨(↑u⁻¹ : V)*z^2,?_⟩
  rw [hT]
  ring

section Chart
variable (pi : V) (u : Vˣ) (a : V) (d b : Fin 3 → V)
/-- The contact coordinate on the dilatation chart. The uniformizer is
NOT inverted; the original distinguished root will be pi*Z. -/
@[expose] def contact : V[X] := C a+C (pi*(↑u⁻¹ : V))*X^2
@[expose] def coefficient (j : Fin 3) : V[X] := C (d j)*(contact pi u a-C (b j))
abbrev Order := ThreeRootOrder318.Order (coefficient pi u a d b)

variable (T y : V) (zOther : Fin 3 → V)
  (hy : y^2=(u : V)*pi*(T-a))
  (hOther : ∀ j,(zOther j)^2=d j*(T-b j))

include hy hOther in
/-- All the other original signed roots descend to one explicit
three-root chart over the integral new coordinate. -/
theorem exists_chart_coordinates (hp : Irreducible pi) :
    ∃ z : V, y=pi*z ∧ Polynomial.eval z (contact pi u a)=T ∧
      ∀ j, (zOther j)^2=Polynomial.eval z (coefficient pi u a d b j) := by
  obtain ⟨z,hz,hT⟩ := exists_coordinate pi hp u a T y hy
  refine ⟨z,hz,?_,?_⟩
  · simpa only [contact,eval_add,eval_C,eval_mul,eval_pow,eval_X] using hT.symm
  · intro j
    simpa only [coefficient,contact,eval_mul,eval_C,eval_sub,eval_add,eval_pow,eval_X,hT]
      using hOther j
end Chart
end OddTwistDilatationCoordinates318
