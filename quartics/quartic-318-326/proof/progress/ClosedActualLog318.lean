module
public import ClosedScaledEvaluation318
public import ReciprocalGroup318
public section
namespace ClosedActualLog318
open ClosedScaledEvaluation318 ReciprocalDouble318 ReciprocalGroup318
variable (p : ℕ) [Fact p.Prime]
noncomputable section
set_option maxHeartbeats 0
local instance : DecidableEq ℚ_[p] := Classical.decEq _

@[expose] def U (x : ℤ_[p]) : ℚ_[p] := (p:ℚ_[p])*(x:ℚ_[p])
@[expose] def V (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) : ℚ_[p] :=
  (valueV p hp D hD x:ℚ_[p])

theorem curve (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    (V p hp D hD x)^2=1-D*(U p x)^4 := by
  have h:=valueV_curve p hp D hD x
  dsimp [V,U]
  convert h using 1 <;> ring

theorem root_binding (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    V p hp D hD x=CanonicalRoot318.root p hp (D*(U p x)^4) := by
  rw [V,valueV_eq_root p hp D hD x]
  congr 1
  dsimp [U]; ring

theorem normalized_zero (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p])
    (hu : U p x=0) : V p hp D hD x=1 := by
  rw [root_binding p hp D hD x,hu,zero_pow (by decide),mul_zero,CanonicalRoot318.root_zero]

theorem normalized_square (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (x y : ℤ_[p]) (hxy : (U p x)^2=(U p y)^2) :
    V p hp D hD x=V p hp D hD y := by
  rw [root_binding p hp D hD x,root_binding p hp D hD y]
  have h4 : (U p x)^4=(U p y)^4 := by
    calc
      _=((U p x)^2)^2 := by ring
      _=((U p y)^2)^2 := by rw [hxy]
      _=_ := by ring
  rw [h4]

theorem denominator_nonzero (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) : 1+D*(U p (z 0))^2*(U p (z 1))^2≠0 := by
  have hd : ‖D*(p:ℚ_[p])^4‖<1 := by
    rw [←ScaledFormalSeries318.coe_parameter p D hD,PadicInt.norm_coe]
    exact parameter_small p D hD
  have he : D*(U p (z 0))^2*(U p (z 1))^2=
      (D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2 := by dsimp [U]; ring
  have hlt : ‖D*(U p (z 0))^2*(U p (z 1))^2‖<1 := by
    rw [he,norm_mul,norm_mul,←PadicInt.coe_pow,←PadicInt.coe_pow,PadicInt.norm_coe,PadicInt.norm_coe]
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (PadicInt.norm_le_one _)).trans_lt
      ((mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans_lt hd)
  intro hq
  have heq : D*(U p (z 0))^2*(U p (z 1))^2= -1 := by linear_combination hq
  rw [heq,norm_neg,norm_one] at hlt
  exact lt_irrefl _ hlt

theorem sumU_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) :
    sumU D (U p (z 0)) (V p hp D hD (z 0)) (U p (z 1)) (V p hp D hD (z 1))=
      U p (sumParameter p hp D hD z) := by
  dsimp only [U]
  rw [sumParameter_eq p hp D hD z]
  dsimp [sumU,V]
  have hd : D*((p:ℚ_[p])*(z 0:ℚ_[p]))^2*((p:ℚ_[p])*(z 1:ℚ_[p]))^2=
      (D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2 := by ring
  rw [hd]
  ring

theorem sumV_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) :
    sumV D (U p (z 0)) (V p hp D hD (z 0)) (U p (z 1)) (V p hp D hD (z 1))=
      V p hp D hD (sumParameter p hp D hD z) := by
  dsimp only [V]
  rw [sumOrdinate_eq p hp D hD z]
  dsimp [sumV,U]
  congr 1 <;> ring

@[expose] def chart (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    (E D).Point := point D (U p x) (V p hp D hD x)
      (valueV_nonzero p hp D hD x) (curve p hp D hD x)

/-- The actual Mathlib elliptic group law agrees with the convergent analytic
parameter law. This assembly covers every u=p*x with x integral, including depth one. -/
theorem chart_add (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) :
    chart p hp D hD (z 0)+chart p hp D hD (z 1)=
      chart p hp D hD (sumParameter p hp D hD z) := by
  have hout : sumV D (U p (z 0)) (V p hp D hD (z 0)) (U p (z 1)) (V p hp D hD (z 1))≠0 := by
    rw [sumV_eq p hp D hD z]
    exact valueV_nonzero p hp D hD _
  have h:=actual_add D (U p (z 0)) (V p hp D hD (z 0)) (U p (z 1)) (V p hp D hD (z 1))
    (valueV_nonzero p hp D hD _) (valueV_nonzero p hp D hD _)
    (curve p hp D hD _) (curve p hp D hD _)
    (normalized_zero p hp D hD _) (normalized_zero p hp D hD _)
    (normalized_square p hp D hD _ _)
    (denominator_nonzero p hp D hD z) hout
  simpa only [chart,sumU_eq p hp D hD z,sumV_eq p hp D hD z] using h

theorem integral_add (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) :
    let t:=sumParameter p hp D hD z;
    -U p t*HTail318.H p (D*(U p t)^4)=
      -U p (z 0)*HTail318.H p (D*(U p (z 0))^4)+
      -U p (z 1)*HTail318.H p (D*(U p (z 1))^4) := by
  have h:=congrArg (fun a : ℚ_[p] => (p:ℚ_[p])*a) (actual_H_addition p hp D hD z)
  dsimp only at h ⊢
  have harg (x : ℤ_[p]) : D*(U p x)^4=D*(p:ℚ_[p])^4*(x:ℚ_[p])^4 := by dsimp [U]; ring
  simp only [harg,U] at *
  linear_combination h

end
end ClosedActualLog318
#print axioms ClosedActualLog318.chart_add
#print axioms ClosedActualLog318.integral_add
