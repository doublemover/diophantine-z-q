module
public import OriginalSparseQuadraticPlane318
public import OriginalUniformSparseSmoothChart318

/-! The full infinity affine locus, not only its two points at z=0.
Its coprimality is transported by polynomial scaling from the swapped
Cowan equation; the MODEL overlap is still the ordinary Laurent overlap. -/
public section
noncomputable section
namespace OriginalSparseReciprocalSmooth318
open OriginalSparseQuadraticCharts318
open OriginalUniformSparseSmoothChart318 (eqVal delta collision relative_coprime)
open Polynomial
variable {R : Type*} [CommRing R]

theorem reverse_scaled (s t z : R) :
    (5-s*t)^3*OriginalUniformSparseReciprocalChart318.reverse s t z =
      eqVal t s ((5-s*t)*z) := by
  unfold OriginalUniformSparseReciprocalChart318.reverse eqVal
  ring

theorem reciprocal_comp (s t : R) :
    C (5-s*t)^3*G s t=(F t s).comp (C (5-s*t)*X) := by
  rw [comp_eq_aeval,aeval_ordinary]
  change C (5-s*t)^3*OriginalUniformSparseReciprocalChart318.reverse (C s) (C t) X =
    eqVal (C t) (C s) (C (5-s*t)*X)
  have h : (5-(C s:R[X])*C t)=C (5-s*t) := by
    rw [map_sub,map_mul,map_ofNat]
  simpa only [h] using reverse_scaled (C s) (C t) (X:R[X])

theorem reciprocal_comp_derivative (s t : R) :
    C (5-s*t)^3*(G s t).derivative =
      C (5-s*t)*((F t s).derivative.comp (C (5-s*t)*X)) := by
  have h := congrArg derivative (reciprocal_comp s t)
  simpa only [← C_pow,derivative_mul,derivative_C,zero_mul,zero_add,
    derivative_comp,derivative_X,mul_one] using h

theorem ordinary_derivative (s t : R) :
    (F s t).derivative=OriginalUniformSparseSmoothChart318.derVal (C s) (C t) X := by
  change (ordinary s t).derivative=_
  unfold ordinary eqVal OriginalUniformSparseSmoothChart318.derVal
  simp [derivative_add,derivative_mul,derivative_pow,C_ofNat]
  ring

theorem ordinary_coprime (s t : R) (unit : IsUnit (delta s t)) :
    IsCoprime (F s t) (F s t).derivative := by
  rcases unit with ⟨q,hq⟩
  have hb := OriginalUniformSparseSmoothChart318.bezout (C s) (C t) X
  change _*F s t + _*OriginalUniformSparseSmoothChart318.derVal (C s) (C t) X = _ at hb
  rw [←ordinary_derivative,OriginalUniformSparseSmoothChart318.delta_cast,←hq] at hb
  refine ⟨C (↑q⁻¹ : R) * OriginalUniformSparseSmoothChart318.u (C s) (C t) X,
    C (↑q⁻¹ : R) * OriginalUniformSparseSmoothChart318.v (C s) (C t) X,?_⟩
  calc
    _ = C (↑q⁻¹ : R) *
      (OriginalUniformSparseSmoothChart318.u (C s) (C t) X*F s t +
       OriginalUniformSparseSmoothChart318.v (C s) (C t) X*(F s t).derivative) := by ring
    _ = 1 := by rw [hb,←map_mul,Units.inv_mul,map_one]

theorem reciprocal_coprime (s t : R) (hw : IsUnit (5-s*t)) (hd : IsUnit (delta t s)) :
    IsCoprime (G s t) (G s t).derivative := by
  obtain ⟨u,v,huv⟩ := ordinary_coprime t s hd
  let q : R[X] := C (5-s*t)*X
  have H := congrArg (compRingHom q) huv
  simp only [map_add,map_mul,map_one,coe_compRingHom_apply] at H
  change u.comp q * (F t s).comp q + v.comp q * (F t s).derivative.comp q=1 at H
  have hwC : IsUnit (C (5-s*t):R[X]) := hw.map C
  obtain ⟨e,he⟩ := hwC
  have hr : (F t s).derivative.comp q = (C (5-s*t))^2 * (G s t).derivative := by
    apply (show IsUnit (C (5-s*t):R[X]) from ⟨e,he⟩).mul_left_cancel
    change C (5-s*t)*(F t s).derivative.comp q =
      C (5-s*t)*(C (5-s*t)^2*(G s t).derivative)
    rw [←reciprocal_comp_derivative]
    ring
  have hG : (F t s).comp q=C (5-s*t)^3*G s t := (reciprocal_comp s t).symm
  rw [hG,hr,←mul_assoc,←mul_assoc] at H
  exact ⟨_,_,H⟩

theorem finite_smooth (s t : R) (h2 : IsUnit (2:R)) (hs : IsUnit (delta s t)) :
    Algebra.Smooth R (CF s t) :=
  OriginalSparseQuadraticPlane318.smooth (F s t) h2 (ordinary_coprime s t hs)

theorem infinity_smooth (s t : R) (h2 : IsUnit (2:R)) (hw : IsUnit (5-s*t))
    (hs : IsUnit (delta t s)) : Algebra.Smooth R (CG s t) :=
  OriginalSparseQuadraticPlane318.smooth (G s t) h2 (reciprocal_coprime s t hw hs)

end OriginalSparseReciprocalSmooth318

#print axioms OriginalSparseReciprocalSmooth318.infinity_smooth
