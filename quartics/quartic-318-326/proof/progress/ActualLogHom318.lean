module
public import ClosedActualLog318
public section
namespace ActualLogHom318
open ClosedActualLog318 ClosedScaledEvaluation318 ReciprocalDouble318 WeierstrassCurve.Affine
variable (p : ℕ) [Fact p.Prime]
noncomputable section
local instance : DecidableEq ℚ_[p] := Classical.decEq _
set_option maxHeartbeats 0

/-- Canonical reciprocal parameter recovered from an actual elliptic point. -/
@[expose] def recover (hp : 19≤p) (D : ℚ_[p]) : (E D).Point → ℚ_[p]
  | .zero => 0
  | .some x y _ => x*CanonicalRoot318.root p hp (D/x^2)/y

theorem recover_chart (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (t : ℤ_[p]) :
    recover p hp D (chart p hp D hD t)=U p t := by
  by_cases hu : U p t=0
  · simp [chart,point,hu,recover]
  · simp only [chart,point,dite_eq_right hu,recover]
    have harg : D/(1/(U p t)^2)^2=D*(U p t)^4 := by field_simp
    rw [harg,←root_binding p hp D hD t]
    have hv : V p hp D hD t≠0 := valueV_nonzero p hp D hD t
    field_simp [hu,hv]

theorem U_injective : Function.Injective (U p) := by
  intro a b h
  apply PadicInt.ext
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h

theorem chart_injective (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) :
    Function.Injective (chart p hp D hD) := by
  intro a b h
  apply U_injective p
  simpa only [recover_chart] using congrArg (recover p hp D) h

theorem chart_zero (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) : chart p hp D hD 0=0 := by
  simp [chart,U,point]

theorem chart_negative (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (t : ℤ_[p]) :
    chart p hp D hD (-t)= -chart p hp D hD t := by
  have hu : U p (-t)= -U p t := by simp [U]
  have hv : V p hp D hD (-t)=V p hp D hD t :=
    normalized_square p hp D hD _ _ (by rw [hu]; ring)
  simpa only [chart,hu,hv] using point_negative D (U p t) (V p hp D hD t)
    (valueV_nonzero p hp D hD t) (curve p hp D hD t)

/-- Actual subgroup of the Mathlib elliptic group parametrized by u∈p Zp. -/
@[expose] def formalSubgroup (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) : AddSubgroup (E D).Point where
  carrier := Set.range (chart p hp D hD)
  zero_mem' := ⟨0,chart_zero p hp D hD⟩
  add_mem' := by
    rintro P Q ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨sumParameter p hp D hD ![a,b],(chart_add p hp D hD ![a,b]).symm⟩
  neg_mem' := by
    rintro P ⟨a,rfl⟩
    exact ⟨-a,chart_negative p hp D hD a⟩

/-- The actual convergent H integral, as a function of an actual curve point. -/
@[expose] def logarithm (hp : 19≤p) (D : ℚ_[p]) (P : (E D).Point) : ℚ_[p] :=
  -recover p hp D P * HTail318.H p (D*(recover p hp D P)^4)

theorem logarithm_chart (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (t : ℤ_[p]) :
    logarithm p hp D (chart p hp D hD t)= -U p t*HTail318.H p (D*(U p t)^4) := by
  rw [logarithm,recover_chart]

theorem logarithm_add (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P Q : formalSubgroup p hp D hD) :
    logarithm p hp D (P.1+Q.1)=logarithm p hp D P.1+logarithm p hp D Q.1 := by
  obtain ⟨a,ha⟩:=P.2
  obtain ⟨b,hb⟩:=Q.2
  have hab : chart p hp D hD a+chart p hp D hD b=chart p hp D hD (sumParameter p hp D hD ![a,b]) := by
    simpa using chart_add p hp D hD ![a,b]
  rw [←ha,←hb,hab]
  simpa only [logarithm_chart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
    integral_add p hp D hD ![a,b]

/-- An actual additive homomorphism on an actual elliptic subgroup. Its
construction does not assume a logarithm homomorphism axiom. -/
@[expose] def logHom (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) :
    formalSubgroup p hp D hD →+ ℚ_[p] where
  toFun P := logarithm p hp D P.1
  map_zero' := by simp [logarithm,recover]
  map_add' := logarithm_add p hp D hD

end
end ActualLogHom318
#print axioms ActualLogHom318.chart_injective
#print axioms ActualLogHom318.logHom
