module
public import LocalIndexRegularity318
public section
noncomputable section
namespace ArithmeticIndexRegularity318
open ConcreteG8Domain (K)
open PadicQuadraticCoordinates318 LocalIndexRegularity318
open scoped QuadraticAlgebra Topology
set_option maxHeartbeats 1000000

@[expose] def QRegular (p : ℕ) [Fact p.Prime] (h₀ : ℤ) (f : ℤ → ℚ) : Prop :=
  Regular h₀ (fun h => (f h:ℚ_[p]))
@[expose] def KRegular (p : ℕ) [Fact p.Prime] (h₀ : ℤ) (f : ℤ → K) : Prop :=
  Regular h₀ (fun h => lift p (f h))

namespace QRegular
variable (p : ℕ) [Fact p.Prime] (h₀ : ℤ)
lemma const (q : ℚ) : QRegular p h₀ (fun _ => q) := constRegular h₀ _
variable {p h₀} {f g : ℤ → ℚ}
lemma add (hf : QRegular p h₀ f) (hg : QRegular p h₀ g) : QRegular p h₀ (fun h => f h+g h) := by
  simpa only [QRegular,Rat.cast_add] using LocalIndexRegularity318.add hf hg
lemma sub (hf : QRegular p h₀ f) (hg : QRegular p h₀ g) : QRegular p h₀ (fun h => f h-g h) := by
  simpa only [QRegular,Rat.cast_sub] using LocalIndexRegularity318.sub hf hg
lemma mul (hf : QRegular p h₀ f) (hg : QRegular p h₀ g) : QRegular p h₀ (fun h => f h*g h) := by
  simpa only [QRegular,Rat.cast_mul] using LocalIndexRegularity318.mul hf hg
lemma neg (hf : QRegular p h₀ f) : QRegular p h₀ (fun h => -f h) := by
  simpa only [QRegular,Rat.cast_neg] using LocalIndexRegularity318.neg hf
lemma pow (hf : QRegular p h₀ f) (n : ℕ) : QRegular p h₀ (fun h => f h^n) := by
  simpa only [QRegular,Rat.cast_pow] using LocalIndexRegularity318.pow hf n
lemma inv (hf : QRegular p h₀ f) (hn : f h₀≠0) : QRegular p h₀ (fun h => (f h)⁻¹) := by
  simpa only [QRegular,Rat.cast_inv] using LocalIndexRegularity318.inv hf (Rat.cast_ne_zero.mpr hn)
lemma div (hf : QRegular p h₀ f) (hg : QRegular p h₀ g) (hn : g h₀≠0) :
    QRegular p h₀ (fun h => f h/g h) := by
  simpa only [div_eq_mul_inv] using mul hf (inv hg hn)
end QRegular

lemma qnorm_lift (p : ℕ) [Fact p.Prime] (x : K) :
    qnorm (lift p x)=(AnchorNorm318.norm x:ℚ_[p]) := by
  simp [qnorm,lift,AnchorNorm318.norm,QuadraticAlgebra.norm_def]
  push_cast
  ring

namespace KRegular
variable (p : ℕ) [Fact p.Prime] (h₀ : ℤ)
lemma const (q : K) : KRegular p h₀ (fun _ => q) := constRegular h₀ _
variable {p h₀} {f g : ℤ → K}
lemma re (hf : KRegular p h₀ f) : QRegular p h₀ (fun h => (f h).re) :=
  comp hf continuous_fst.continuousAt
lemma im (hf : KRegular p h₀ f) : QRegular p h₀ (fun h => (f h).im) :=
  comp hf continuous_snd.continuousAt
lemma of_pair {f g : ℤ → ℚ} (hf : QRegular p h₀ f) (hg : QRegular p h₀ g) :
    KRegular p h₀ (fun h => ConcreteG8Domain.pair (f h) (g h)) := pair hf hg
lemma add (hf : KRegular p h₀ f) (hg : KRegular p h₀ g) : KRegular p h₀ (fun h => f h+g h) := by
  have he : Regular h₀ (fun h => lift p (f h)+lift p (g h)) := comp (pair hf hg) (by fun_prop)
  simpa only [KRegular,lift_add] using he
lemma sub (hf : KRegular p h₀ f) (hg : KRegular p h₀ g) : KRegular p h₀ (fun h => f h-g h) := by
  have he : Regular h₀ (fun h => lift p (f h)-lift p (g h)) := comp (pair hf hg) (by fun_prop)
  simpa only [KRegular,lift_sub] using he
lemma mul (hf : KRegular p h₀ f) (hg : KRegular p h₀ g) : KRegular p h₀ (fun h => f h*g h) := by
  have he := comp (pair hf hg) mul_continuous.continuousAt
  simpa only [KRegular,lift_mul] using he
lemma neg (hf : KRegular p h₀ f) : KRegular p h₀ (fun h => -f h) := by
  simpa only [zero_sub] using sub (const p h₀ 0) hf
lemma pow (hf : KRegular p h₀ f) (n : ℕ) : KRegular p h₀ (fun h => f h^n) := by
  induction n with
  | zero => simpa only [pow_zero] using const p h₀ 1
  | succ n ih => simpa only [pow_succ] using mul ih hf
lemma inv (hf : KRegular p h₀ f) (hn : f h₀≠0) : KRegular p h₀ (fun h => (f h)⁻¹) := by
  have hnorm : qnorm (lift p (f h₀))≠0 := by
    rw [qnorm_lift]
    exact Rat.cast_ne_zero.mpr (AnchorNorm318.norm_ne_zero hn)
  have he := comp hf (inverse_continuousAt hnorm)
  simpa only [KRegular,lift_inverse] using he
lemma div (hf : KRegular p h₀ f) (hg : KRegular p h₀ g) (hn : g h₀≠0) :
    KRegular p h₀ (fun h => f h/g h) := by
  simpa only [div_eq_mul_inv] using mul hf (inv hg hn)
end KRegular

variable (p : ℕ) [Fact p.Prime]
  (hb : ∀ e : ℕ, ∀ m : ℤ, ‖ActualOrbitLocalFilter318.error p (4*6^e*m)‖≤((p:ℝ)⁻¹)^e)

include hb in
lemma chartU (a b h₀ : ℤ) :
    KRegular p h₀ (fun h => CoherentMultipleCharts318.chartU (a+b*h)) := by
  have he := comp (actual_chart p hb a b h₀)
    (show ContinuousAt ActualOrbitTranslatedAccess318.inputU _ by
      unfold ActualOrbitTranslatedAccess318.inputU; fun_prop)
  simpa only [KRegular,ActualOrbitTranslatedAccess318.inputU_error] using he
include hb in
lemma chartV (a b h₀ : ℤ) :
    KRegular p h₀ (fun h => CoherentMultipleCharts318.chartV (a+b*h)) := by
  have he := comp (actual_chart p hb a b h₀)
    (show ContinuousAt ActualOrbitTranslatedAccess318.inputV _ by
      unfold ActualOrbitTranslatedAccess318.inputV; fun_prop)
  simpa only [KRegular,ActualOrbitTranslatedAccess318.inputV_error] using he

end ArithmeticIndexRegularity318

/-- Close polynomial regularity goals by the proved closure rules only.
Any inverse domain left by those rules remains an ordinary proof obligation. -/
macro "index_regularity" : tactic => `(tactic|
  aesop (add safe apply ArithmeticIndexRegularity318.QRegular.add)
    (add safe apply ArithmeticIndexRegularity318.QRegular.sub)
    (add safe apply ArithmeticIndexRegularity318.QRegular.mul)
    (add safe apply ArithmeticIndexRegularity318.QRegular.neg)
    (add safe apply ArithmeticIndexRegularity318.QRegular.pow)
    (add safe apply ArithmeticIndexRegularity318.QRegular.const)
    (add safe apply ArithmeticIndexRegularity318.KRegular.re)
    (add safe apply ArithmeticIndexRegularity318.KRegular.im)
    (add safe apply ArithmeticIndexRegularity318.KRegular.add)
    (add safe apply ArithmeticIndexRegularity318.KRegular.sub)
    (add safe apply ArithmeticIndexRegularity318.KRegular.mul)
    (add safe apply ArithmeticIndexRegularity318.KRegular.neg)
    (add safe apply ArithmeticIndexRegularity318.KRegular.pow)
    (add safe apply ArithmeticIndexRegularity318.KRegular.const)
    (add safe apply ArithmeticIndexRegularity318.KRegular.of_pair))
