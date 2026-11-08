module
public import InfinityRingHomExt318
public section
noncomputable section
namespace InfinityDiagonalDivisibility318
open InfinityReciprocalAction318 InfinityOrderCoordinates318 InfinitySignCoordinates318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
@[expose] def ideal:Ideal (Order c):=Ideal.span {coordinate c}
abbrev Quotient:=Order c ⧸ ideal c
local instance quotientRing:CommRing (Quotient c):=Ideal.Quotient.commRing (ideal c)
local instance quotientRat:Algebra ℚ (Quotient c):=by
  let f:ℚ→+*Quotient c:=(Ideal.Quotient.mk (ideal c)).comp (algebraMap ℚ (Order c))
  exact f.toAlgebra
/-- The actual all-four root sign is identity on the entire u=0 quotient,
not merely after passage to prime quotients or geometric residue fields. -/
theorem quotient_fixed (x:Order c):
    Ideal.Quotient.mk (ideal c) (sign c (fun _=>true) x)=Ideal.Quotient.mk (ideal c) x:=by
  have h:(Ideal.Quotient.mk (ideal c)).comp (sign c (fun _=>true)).toRingHom=
      Ideal.Quotient.mk (ideal c):=by
    apply InfinityRingHomExt318.hom_ext (F:=Quotient c) c
    · change Ideal.Quotient.mk (ideal c) (sign c (fun _=>true) (coordinate c))=_
      rw [on_coordinate]
      have hz:Ideal.Quotient.mk (ideal c) (coordinate c)=0:=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      simp only [ite_true,map_neg,hz,neg_zero]
    · intro j
      change Ideal.Quotient.mk (ideal c) (sign c (fun _=>true) (generator c j))=_
      rw [on_generator]
      rfl
  exact RingHom.congr_fun h x
/-- Anti-invariant regular coefficients are divisible by the actual u
coordinate. Cancellation uses the unit2, not reducedness of the quotient. -/
theorem divisible (x:Order c) (hx:sign c (fun _=>true) x= -x):coordinate c ∣ x:=by
  have h:=quotient_fixed c x
  rw [hx,map_neg] at h
  have htwo:(2:Quotient c)*Ideal.Quotient.mk (ideal c) x=0:=by
    linear_combination -h
  have hunit:IsUnit (2:Quotient c):=by
    simpa only [map_ofNat] using (IsUnit.mk0 (2:ℚ) (by norm_num)).map (algebraMap ℚ (Quotient c))
  have hz:Ideal.Quotient.mk (ideal c) x=0:=by
    exact hunit.mul_right_eq_zero.mp htwo
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
end InfinityDiagonalDivisibility318
