module
public import OriginalSparseSmoothProper318
public import OriginalMarkedScalarSeparableTrace318

/-! The proper sparse model at the SAME original labeled scalar mark used
for the uniform trace, with no separate nonsingularity hypothesis. -/
public section
namespace OriginalMarkedSparseProper318

open AlgebraicGeometry
open OriginalUniformCentralTwistTransport318 OriginalUniformMarkedQMSurface318
open OriginalUniformSparseSmoothChart318 (collision)
open OriginalMarkedScalarSeparableTrace318 (core_on)
open OriginalUniformSparseIgusa318 (i10 reads_factored)
open OriginalSparseGluedScheme318
variable {K : Type*} [Field K] [CharZero K]

theorem nonzero_igusa (d : Row K) (R u : K) (h : Laws d) (hh : Sheet d R u) :
    i10 (d.m+R) (d.m-R) ≠ 0 := by
  let s:=d.m+R
  let t:=d.m-R
  have hcore : collision s t = OriginalUniversalSparsePolynomial318.core s t := by
    unfold collision OriginalUniversalSparsePolynomial318.core
    ring
  have he : collision s t ≠ 0 := by
    rw [hcore,core_on d R u hh]
    exact h.nzE
  have hn : s*t ≠ 0 := hh.st.symm ▸ h.nzN
  have hg : s*t-5 ≠ 0 := hh.st.symm ▸ h.nzGap
  have hi := (reads_factored s t).2.2.2
  change i10 s t=200000*(collision s t)^2*(s*t)^10*(s*t-5)^10 at hi
  change i10 s t≠0
  rw [hi]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ he)) (pow_ne_zero _ hn))
    (pow_ne_zero _ hg)

/-- The marked coefficient field and sparse s,t are literally the same
as the existing original marked separable trace endpoint. -/
theorem from_original (x:ℚ) (r₀ r₁ r₂ r₃ v:K) (hx:x≠0)
    (h₀:r₀^2= -14*(119136*(x:K)^2)) (h₁:r₁^2= -6*(119136*(x:K)^2-32))
    (h₂:r₂^2=42*(119136*(x:K)^2-76832)) (h₃:r₃^2= -21*(119136*(x:K)^2+343))
    (hv:v^2=5) :
    let d:=row (zCoord r₀ r₁ r₃)
    let R:=discRoot d v r₂
    Smooth (structureMap (d.m+R) (d.m-R)) ∧
      IsProper (structureMap (d.m+R) (d.m-R)) := by
  let H:=OriginalUniformMarkedQMSurface318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
  exact OriginalSparseSmoothProper318.smooth_proper_of_igusa _ _
    (nonzero_igusa _ _ _ H.actual_laws H.marked)

end OriginalMarkedSparseProper318

#print axioms OriginalMarkedSparseProper318.from_original
