module
public import ActualTwoDescentLocalValuationTools318
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public section

noncomputable section

namespace CTNativePadicUnitNormalization318

open ActualTwoDescentLocalValuationTools318

variable (p : ℕ) [Fact p.Prime]

theorem padic_prime_ne : (p:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- Literal normalization by the actual uniformizer p to the signed
valuation. Works on all nonzero field values, including negative order. -/
@[expose] def normalizedField (x : ℚ_[p]ˣ) : ℚ_[p] :=
  (x:ℚ_[p])/(p:ℚ_[p])^((x:ℚ_[p]).valuation)

theorem normalizedField_ne (x : ℚ_[p]ˣ) : normalizedField p x≠0 :=
  div_ne_zero x.ne_zero (zpow_ne_zero _ (padic_prime_ne p))

theorem uniformizer_valuation (z : ℤ) : ((p:ℚ_[p])^z).valuation=z := by
  rw [Padic.valuation_zpow,Padic.valuation_p,mul_one]

theorem normalized_valuation (x : ℚ_[p]ˣ) : (normalizedField p x).valuation=0 := by
  unfold normalizedField
  rw [actual_valuation_div _ _ x.ne_zero (zpow_ne_zero _ (padic_prime_ne p)),
    uniformizer_valuation p,sub_self]

def normalizedInteger (x : ℚ_[p]ˣ) : ℤ_[p] :=
  ⟨normalizedField p x,(Padic.norm_le_one_iff_val_nonneg (normalizedField p x)).mpr
    (normalized_valuation p x).ge⟩

theorem normalizedIntegralUnit (x : ℚ_[p]ˣ) : IsUnit (normalizedInteger p x) := by
  apply PadicInt.isUnit_iff.mpr
  change ‖normalizedField p x‖=1
  exact actual_norm_one_of_valuation_zero _ (normalizedField_ne p x) (normalized_valuation p x)

def normalizedUnit (x : ℚ_[p]ˣ) : ℤ_[p]ˣ := (normalizedIntegralUnit p x).unit

theorem normalizedUnit_field (x : ℚ_[p]ˣ) :
    (((normalizedUnit p x:ℤ_[p]ˣ):ℤ_[p]):ℚ_[p])=normalizedField p x :=
  congrArg (fun u : ℤ_[p] => (u:ℚ_[p])) (normalizedIntegralUnit p x).unit_spec

theorem normalizedField_mul (x y : ℚ_[p]ˣ) :
    normalizedField p (x*y)=normalizedField p x*normalizedField p y := by
  unfold normalizedField
  rw [Units.val_mul,Padic.valuation_mul x.ne_zero y.ne_zero,zpow_add₀ (padic_prime_ne p)]
  have hx : (p:ℚ_[p])^((x:ℚ_[p]).valuation)≠0 := zpow_ne_zero _ (padic_prime_ne p)
  have hy : (p:ℚ_[p])^((y:ℚ_[p]).valuation)≠0 := zpow_ne_zero _ (padic_prime_ne p)
  field_simp [hx,hy] <;> ring

/-- Normalization is multiplicative on the same actual units, not just
a choice of one unit in a squareclass. -/
def normalizeHom : ℚ_[p]ˣ →* ℤ_[p]ˣ where
  toFun := normalizedUnit p
  map_one' := by
    apply Units.ext
    apply PadicInt.ext
    rw [normalizedUnit_field]
    change normalizedField p (1:ℚ_[p]ˣ)=1
    rw [normalizedField,Units.val_one,Padic.valuation_one,zpow_zero,div_one]
  map_mul' x y := by
    apply Units.ext
    apply PadicInt.ext
    change (((normalizedUnit p (x*y):ℤ_[p]ˣ):ℤ_[p]):ℚ_[p]) =
      (((normalizedUnit p x*normalizedUnit p y:ℤ_[p]ˣ):ℤ_[p]):ℚ_[p])
    rw [Units.val_mul,PadicInt.coe_mul,normalizedUnit_field,normalizedUnit_field,
      normalizedUnit_field,normalizedField_mul]

theorem field_factorization (x : ℚ_[p]ˣ) :
    (x:ℚ_[p])=(p:ℚ_[p])^((x:ℚ_[p]).valuation)*normalizedField p x := by
  unfold normalizedField
  rw [mul_comm,div_mul_cancel₀ _ (zpow_ne_zero _ (padic_prime_ne p))]

theorem normalized_of_valuation_zero (x : ℚ_[p]ˣ) (h : (x:ℚ_[p]).valuation=0) :
    normalizedField p x=(x:ℚ_[p]) := by rw [normalizedField,h,zpow_zero,div_one]

theorem normalized_prime_field :
    normalizedField p (Units.mk0 (p:ℚ_[p]) (padic_prime_ne p))=1 := by
  unfold normalizedField
  rw [Units.val_mk0,Padic.valuation_p,zpow_one,div_self (padic_prime_ne p)]

end CTNativePadicUnitNormalization318

#print axioms CTNativePadicUnitNormalization318.normalizeHom
#print axioms CTNativePadicUnitNormalization318.normalized_prime_field
