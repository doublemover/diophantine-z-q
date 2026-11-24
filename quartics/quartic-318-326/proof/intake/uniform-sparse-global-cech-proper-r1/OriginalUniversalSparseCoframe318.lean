module
public import OriginalUniversalSparseTrace318
public import OriginalUniformMarkedMatrices318
public section
noncomputable section
namespace OriginalUniversalSparseCoframe318
open Polynomial OriginalUniversalSparsePolynomial318 OriginalUniversalSparseTrace318
open OriginalSexticJetMarked318 OriginalSeparableSexticJet318
open OriginalUniformSparseJet318 OriginalUniformMarkedQMSurface318
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
variable {K : Type*} [Field K] [CharZero K]
@[expose] def at0 {R : Type*} [Zero R] (l : List R) (i : ℕ) : R := (l[i]?).getD 0
omit [CharZero K] in
/-- This is the actual derivative of every coefficient of F along the two-dimensional
direction, before specialization; no assignment of six independent branch velocities. -/
theorem coeff_direction (s t ds dt : K) (i : Fin 7) :
    (at0 (cvec (C s + X*C ds) (C t + X*C dt)) i).derivative.eval 0 =
      ds*at0 (gS s t) i+dt*at0 (gT s t) i := by
  fin_cases i <;> simp [at0,cvec,gS,gT,derivative_pow,derivative_mul] <;> ring

/-- Igusa-Clebsch I₂(F)=-120(F,F)_6 on the literal sparse (not monic-rescaled) coefficients. -/
@[expose] def I2F (s t : K) : K :=
  let v := cvec s t; (-240:K)*at0 v 0*at0 v 6+40*at0 v 1*at0 v 5+6*(at0 v 3)^2
omit [CharZero K] in
theorem i2_factor (s t : K) : I2F s t=200*(s*t)^2*(s*t-5)^2*(2*(s*t)-3) := by
  simp [I2F,cvec,at0]; ring
theorem factor_eq (s t : K) (hs : s≠0) (ht : t≠0)
    (hw : s*t-5≠0) (he : core s t≠0) :
    factor s t=1/(5*(s*t)^2*(s*t-5)^2*core s t) := by
  simp only [OriginalUniversalSparseTrace318.factor,denom,jachead]
  field_simp
  ring
omit [CharZero K] in
theorem moment_read (s t ds dt : K) (hs : s≠0) (hd : denom s t≠0) (i : Fin 3) :
    moment (splittingCertificate (data s t ds dt hs hd)) i =
      factor s t*(diagS s t i*ds+diagT s t i*dt) := by
  exact entry s t ds dt hs hd i
omit [CharZero K] in
theorem diag_det (s t ds dt : K) (hs : s≠0) (hd : denom s t≠0) :
    rawB (splittingCertificate (data s t ds dt hs hd))=factor s t^2*
      ((H00 s t*ds+H10 s t*dt)*(H02 s t*ds+H12 s t*dt)) := by
  simp only [rawB,moment_read]
  simp [diagS,diagT]; ring
theorem pair_id (s t ds dt m : K) (hm : s+t=2*m) :
    (H00 s t*ds+H10 s t*dt)*(H02 s t*ds+H12 s t*dt) =
      (s*t)*(s*t-5)*(factorA (s*t) s t*ds^2+factorA (s*t) t s*dt^2-
        2*(s*t)*cross m (s*t)*ds*dt) := by
  have hm' : m=(s+t)/2 := by linear_combination (-1/2)*hm
  rw [hm']
  simp only [H00,H02,H10,H12,factorA,cross]
  ring
theorem j2_raw (s t ds dt m : K) (hm : s+t=2*m) (hs : s≠0) (ht : t≠0)
    (hw : s*t-5≠0) (he : core s t≠0) (hd : denom s t≠0) :
    I2F s t * rawB (splittingCertificate (data s t ds dt hs hd)) =
      8*(2*(s*t)-3)/((s*t)*(s*t-5)*(core s t)^2)*
      (factorA (s*t) s t*ds^2+factorA (s*t) t s*dt^2-2*(s*t)*cross m (s*t)*ds*dt) := by
  rw [diag_det,pair_id s t ds dt m hm,i2_factor,factor_eq s t hs ht hw he]
  field_simp
  ring
end OriginalUniversalSparseCoframe318
#print axioms OriginalUniversalSparseCoframe318.j2_raw
