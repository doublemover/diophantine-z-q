module
public import PELOriginalWholeHZeroDimension318
public section
noncomputable section
namespace PELOriginalSectionMultiplication318
open QuaternionicRealPeriod318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalPolarizationPowerBundle318
open PELOriginalWholeHZeroDimension318
variable (τ:ℂ)(hτ:0<τ.im)
/-- Genuine original section coefficients in the selected original
fiber gauges. This uses the existing full local-holomorphy H0 predicate,
not a space defined by its theta span, and includes degree zero. -/
abbrev Values:=Base τ→ℂ
@[expose] def homogeneous(n:ℕ):Submodule ℂ (Values τ):=HZero τ hτ n
lemma coefficient_product(m n:ℕ)(s t:Values τ)(a z:ComplexVectors):
    localCoefficient τ hτ (m+n) a (s*t) z=
      localCoefficient τ hτ m a s z*localCoefficient τ hτ n a t z:=by
  simp only [coefficient_formula,Pi.mul_apply,pow_add]
  ring
lemma product_mem(m n:ℕ)(s t:Values τ)
    (hs:s∈homogeneous τ hτ m)(ht:t∈homogeneous τ hτ n):
    s*t∈homogeneous τ hτ (m+n):=by
  intro a
  have he:localCoefficient τ hτ (m+n) a (s*t)=
      fun z=>localCoefficient τ hτ m a s z*localCoefficient τ hτ n a t z:=by
    funext z
    exact coefficient_product τ hτ m n s t a z
  rw [he]
  exact (hs a).mul (ht a)
lemma constant_mem(c:ℂ):(fun _:Base τ=>c)∈homogeneous τ hτ 0:=by
  intro a
  have he:localCoefficient τ hτ 0 a (fun _:Base τ=>c)=fun _=>c:=by
    funext z
    simp only [coefficient_formula,pow_zero,one_mul]
  rw [he]
  exact differentiableOn_const c

/-- Actual bilinear multiplication of original power-line sections.
The degree adds because the SAME original transition factors multiply. -/
@[expose] def multiply(m n:ℕ):homogeneous τ hτ m→ₗ[ℂ]
    homogeneous τ hτ n→ₗ[ℂ]homogeneous τ hτ (m+n) where
  toFun s:=
    {toFun:=fun t=>⟨s.val*t.val,product_mem τ hτ m n s.val t.val s.property t.property⟩
     map_add':=by intro t u;apply Subtype.ext;exact mul_add _ _ _
     map_smul':=by intro c t;apply Subtype.ext;funext q;simp only [Pi.mul_apply,Pi.smul_apply,smul_eq_mul];ring}
  map_add' s t:=by ext u q;exact add_mul _ _ _
  map_smul' c s:=by ext t q;simp only [Pi.mul_apply,Pi.smul_apply,smul_eq_mul];ring
lemma multiply_value(m n:ℕ)(s:homogeneous τ hτ m)(t:homogeneous τ hτ n)(q:Base τ):
    (multiply τ hτ m n s t).val q=s.val q*t.val q:=rfl

/-- The actual recovered original entire representatives multiply too;
no new automorphy or scalar factor is introduced on the universal cover. -/
lemma lift_product(m n:ℕ)(s:homogeneous τ hτ m)(t:homogeneous τ hτ n)(z:ComplexVectors):
    PELOriginalPowerSectionLift318.lift τ hτ (m+n)
      (asSection τ hτ (m+n) (multiply τ hτ m n s t)) z=
    PELOriginalPowerSectionLift318.lift τ hτ m (asSection τ hτ m s) z*
      PELOriginalPowerSectionLift318.lift τ hτ n (asSection τ hτ n t) z:=by
  simp only [PELOriginalPowerSectionLift318.lift,PELOriginalPowerSectionLift318.gauge,
    asSection,multiply_value,pow_add,mul_inv_rev]
  ring
end PELOriginalSectionMultiplication318
