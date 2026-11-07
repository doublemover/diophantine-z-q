module
public import ScaledEvaluation318
public import ReciprocalGroup318
public section
namespace ActualLogAddition318
open ScaledEvaluation318 ReciprocalDouble318 ReciprocalGroup318
variable (p : ℕ) [Fact p.Prime]
noncomputable section
set_option maxHeartbeats 0
local instance : DecidableEq ℚ_[p] := Classical.decEq _

@[expose] def U (x : ℤ_[p]) : ℚ_[p] := (p:ℚ_[p])*(x:ℚ_[p])
@[expose] def V (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) : ℚ_[p] :=
  (valueV p hp D hD x:ℚ_[p])

theorem curve (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    (V p hp D hD x)^2=1-D*(U p x)^4 := by
  have h:=valueV_curve p hp D hD x hx
  dsimp [V,U]
  convert h using 1 <;> ring

theorem root_binding (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    V p hp D hD x=CanonicalRoot318.root p hp (D*(U p x)^4) := by
  rw [V,valueV_eq_root p hp D hD x hx]
  congr 1
  dsimp [U]; ring

theorem normalized_zero (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1)
    (hu : U p x=0) : V p hp D hD x=1 := by
  rw [root_binding p hp D hD x hx,hu,zero_pow (by decide),mul_zero,CanonicalRoot318.root_zero]

theorem normalized_square (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (x y : ℤ_[p]) (hx : ‖x‖<1) (hy : ‖y‖<1) (hxy : (U p x)^2=(U p y)^2) :
    V p hp D hD x=V p hp D hD y := by
  rw [root_binding p hp D hD x hx,root_binding p hp D hD y hy]
  have h4 : (U p x)^4=(U p y)^4 := by
    calc
      _=((U p x)^2)^2 := by ring
      _=((U p y)^2)^2 := by rw [hxy]
      _=_ := by ring
  rw [h4]

theorem denominator_nonzero (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) : 1+D*(U p (z 0))^2*(U p (z 1))^2≠0 := by
  have hd : ‖D*(p:ℚ_[p])^4‖≤1 := by
    rw [←ScaledFormalSeries318.coe_parameter p D hD,PadicInt.norm_coe]
    exact PadicInt.norm_le_one _
  have he : D*(U p (z 0))^2*(U p (z 1))^2=
      (D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2 := by dsimp [U]; ring
  have hlt : ‖D*(U p (z 0))^2*(U p (z 1))^2‖<1 := by
    rw [he,norm_mul,norm_mul,norm_pow,norm_pow,PadicInt.norm_coe,PadicInt.norm_coe]
    have h0 := pow_lt_one₀ (norm_nonneg (z 0)) (hz 0) (by decide : (2:ℕ)≠0)
    have h1 := pow_le_one₀ (norm_nonneg (z 1)) (hz 1).le (n:=2)
    calc
      _ ≤ ‖z 0‖^2*‖z 1‖^2 := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hd) (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖z 0‖^2 := mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) h1
      _ < 1 := h0
  intro hq
  have heq : D*(U p (z 0))^2*(U p (z 1))^2= -1 := by linear_combination hq
  rw [heq,norm_neg,norm_one] at hlt
  exact lt_irrefl _ hlt

theorem sumU_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    sumU D (U p (z 0)) (V p hp D hD (z 0)) (U p (z 1)) (V p hp D hD (z 1))=
      U p (sumParameter p hp D hD z) := by
  dsimp only [U]
  rw [sumParameter_eq p hp D hD z hz]
  dsimp [sumU,V]
  have hd : D*((p:ℚ_[p])*(z 0:ℚ_[p]))^2*((p:ℚ_[p])*(z 1:ℚ_[p]))^2=
      (D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2 := by ring
  rw [hd]
  ring

theorem sumV_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    sumV D (U p (z 0)) (V p hp D hD (z 0)) (U p (z 1)) (V p hp D hD (z 1))=
      V p hp D hD (sumParameter p hp D hD z) := by
  dsimp only [V]
  rw [sumOrdinate_eq p hp D hD z hz]
  dsimp [sumV,U]
  congr 1 <;> ring

@[expose] def chart (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    (E D).Point := point D (U p x) (V p hp D hD x)
      (valueV_nonzero p hp D hD x hx) (curve p hp D hD x hx)

/-- The actual Mathlib elliptic group law agrees with the convergent analytic
parameter law. This first assembly covers u=p*x with norm x<1. -/
theorem chart_add (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    chart p hp D hD (z 0) (hz 0)+chart p hp D hD (z 1) (hz 1)=
      chart p hp D hD (sumParameter p hp D hD z) (sumParameter_small p hp D hD z hz) := by
  have hout : sumV D (U p (z 0)) (V p hp D hD (z 0)) (U p (z 1)) (V p hp D hD (z 1))≠0 := by
    rw [sumV_eq p hp D hD z hz]
    exact valueV_nonzero p hp D hD _ (sumParameter_small p hp D hD z hz)
  have h:=actual_add D (U p (z 0)) (V p hp D hD (z 0)) (U p (z 1)) (V p hp D hD (z 1))
    (valueV_nonzero p hp D hD _ (hz 0)) (valueV_nonzero p hp D hD _ (hz 1))
    (curve p hp D hD _ (hz 0)) (curve p hp D hD _ (hz 1))
    (normalized_zero p hp D hD _ (hz 0)) (normalized_zero p hp D hD _ (hz 1))
    (normalized_square p hp D hD _ _ (hz 0) (hz 1))
    (denominator_nonzero p hp D hD z hz) hout
  simpa only [chart,sumU_eq p hp D hD z hz,sumV_eq p hp D hD z hz] using h

theorem integral_add (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    let t:=sumParameter p hp D hD z;
    -U p t*HTail318.H p (D*(U p t)^4)=
      -U p (z 0)*HTail318.H p (D*(U p (z 0))^4)+
      -U p (z 1)*HTail318.H p (D*(U p (z 1))^4) := by
  have h:=congrArg (fun a : ℚ_[p] => (p:ℚ_[p])*a) (actual_H_addition p hp D hD z hz)
  dsimp only at h ⊢
  have harg (x : ℤ_[p]) : D*(U p x)^4=D*(p:ℚ_[p])^4*(x:ℚ_[p])^4 := by dsimp [U]; ring
  simp only [harg,U] at *
  linear_combination h

end
end ActualLogAddition318
#print axioms ActualLogAddition318.chart_add
#print axioms ActualLogAddition318.integral_add
