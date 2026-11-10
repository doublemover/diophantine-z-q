module
public import ContactArithmeticBase318
public section
noncomputable section
namespace ContactArithmeticTwists318
open ContactArithmeticDenominator318 ContactArithmeticBase318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

@[expose] def numeratorUnit (i : Fin 4) : (Base c)ˣ :=
  (factor_unit c _ (numerator_dvd c i)).unit
@[expose] def denominatorUnit (i : Fin 4) : (Base c)ˣ :=
  (factor_unit c _ (denominator_dvd c i)).unit
/-- The original signed rational twist, as an actual unit in the explicit
arithmetic base. No new squareclass or twist representative is selected. -/
@[expose] def twist (i : Fin 4) : (Base c)ˣ := numeratorUnit c i * (denominatorUnit c i)⁻¹

@[simp] theorem numeratorUnit_value (i : Fin 4) :
    (numeratorUnit c i:Base c)=algebraMap ℤ (Base c) (c i : ℚ).num := IsUnit.unit_spec _
@[simp] theorem denominatorUnit_value (i : Fin 4) :
    (denominatorUnit c i:Base c)=algebraMap ℤ (Base c) ((c i : ℚ).den:ℤ) := IsUnit.unit_spec _

theorem denominator_inverse_value (i : Fin 4) :
    intoQ c ((denominatorUnit c i)⁻¹: (Base c)ˣ)=((c i : ℚ).den:ℚ)⁻¹ := by
  have h := congrArg (intoQ c) (Units.mul_inv (denominatorUnit c i))
  rw [map_mul,map_one,denominatorUnit_value,intoQ_integer,Int.cast_natCast] at h
  exact eq_inv_of_mul_eq_one_right h

/-- Exact comparison with each ORIGINAL rational coefficient under the
specified arithmetic-base embedding. -/
theorem twist_value (i : Fin 4) : intoQ c (twist c i:Base c)=(c i:ℚ) := by
  change intoQ c ((numeratorUnit c i:Base c)*((denominatorUnit c i)⁻¹:(Base c)ˣ))=_
  rw [map_mul,numeratorUnit_value,intoQ_integer,denominator_inverse_value,←div_eq_mul_inv]
  exact (c i : ℚ).num_div_den

theorem twist_map : Units.map (intoQ c).toMonoidHom ∘ twist c=c := by
  funext i
  apply Units.ext
  exact twist_value c i
end ContactArithmeticTwists318
