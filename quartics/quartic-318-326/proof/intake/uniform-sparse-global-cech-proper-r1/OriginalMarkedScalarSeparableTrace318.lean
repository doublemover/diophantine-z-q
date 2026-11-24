module
public import OriginalUniversalSparseCoframe318
public import OriginalUniformCentralTwistTransport318
public section
noncomputable section
namespace OriginalMarkedScalarSeparableTrace318
open Polynomial OriginalUniversalSparsePolynomial318 OriginalUniversalSparseTrace318
open OriginalUniversalSparseCoframe318 OriginalSeparableSexticJet318 OriginalUniformSparseJet318
open OriginalUniformCentralTwistTransport318 OriginalUniformMarkedQMSurface318
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
omit [CharZero K] in
theorem literal_coeff (s t : K) : (sextic s t).coeff=OriginalUniformSparseIgusa318.sparse s t := by
  funext i
  rw [sextic,pol_coeff]
  match i with
  | 0 | 1 | 2 | 4 | 5 | 6 => rfl
  | 3 => simp [cvec,OriginalUniformSparseIgusa318.sparse]; ring
  | _+7 => rfl
theorem raw_i2 (s t : K) : rawI2 (sextic s t)=I2F s t := by
  rw [rawI2,literal_coeff]
  change OriginalUniformSparseIgusa318.i2 s t=_
  rw [(OriginalUniformSparseIgusa318.reads_factored s t).1,i2_factor]
  ring
omit [CharZero K] in
theorem core_on (d : Row K) (R u : K) (hh : Sheet d R u) :
    core (d.m+R) (d.m-R)=(d.n^2-5*d.n)*(2*d.m)+10*d.n^2-90*d.n+216 := by
  unfold core; rw [hh.st]; ring
theorem denom_on (d : Row K) (R u : K) (h : Laws d) (hh : Sheet d R u) :
    denom (d.m+R) (d.m-R)≠0 := by
  simp only [denom,hh.st,core_on d R u hh]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh.s_ne)
    (pow_ne_zero _ hh.t_ne)) (pow_ne_zero _ h.nzGap)) h.nzE
@[expose] def sexticData (d : Row K) (R u : K) (h : Laws d) (hh : Sheet d R u) : Data K :=
  data (d.m+R) (d.m-R) (ps d.m d.p d.q R/(2*R)) (pt d.m d.p d.q R/(2*R))
    hh.s_ne (denom_on d R u h hh)
theorem trace_on_sheet (d : Row K) (R u : K) (h : Laws d) (hh : Sheet d R u) :
    rawI2 (sexticData d R u h hh).F/d.J*detMoment (sexticData d R u h hh) = -10080/(d.X*d.Y) := by
  let s:=d.m+R
  let t:=d.m-R
  let ds:=ps d.m d.p d.q R/(2*R)
  let dt:=pt d.m d.p d.q R/(2*R)
  have he : core s t≠0 := (core_on d R u hh).symm ▸ h.nzE
  have hw : s*t-5≠0 := hh.st.symm ▸ h.nzGap
  have hm : s+t=2*d.m := by dsimp [s,t]; ring
  have hraw := j2_raw s t ds dt d.m hm hh.s_ne hh.t_ne hw he (denom_on d R u h hh)
  change rawI2 (sextic s t)/d.J * OriginalSexticJetMarked318.rawB
    (splittingCertificate (data s t ds dt hh.s_ne (denom_on d R u h hh)))=_
  rw [raw_i2,div_mul_eq_mul_div, hraw,← hh.evalKS]
  unfold normalizedKS detNumerator
  dsimp only [s,t,ds,dt]
  rw [hh.st,core_on d R u hh,← hh.root_eq]
  have hr:=hh.root_ne
  have hJ:=h.nzJ
  have hn:=h.nzN
  have hg:=h.nzGap
  have hE:=h.nzE
  unfold OriginalUniformSparseJet318.delta
  field_simp
  ring

/-- Normalized true raw residue determinant for the actual four labelled radicals on
every nonzero rational scalar fibre; both the degree-six and first-jet polynomial are constructed. -/
theorem from_original (x : ℚ) (r₀ r₁ r₂ r₃ v : K) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₂ : r₂^2=42*(119136*(x:K)^2-76832)) (h₃ : r₃^2= -21*(119136*(x:K)^2+343))
    (hv : v^2=5) :
    let d:=row (zCoord r₀ r₁ r₃)
    let R:=discRoot d v r₂
    let h:=OriginalUniformMarkedQMSurface318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
    let J:=sexticData d R (qCoeff d r₀ R) h.actual_laws h.marked
    rawI2 J.F/d.J * detMoment J = -10080/(d.X*d.Y) := by
  exact trace_on_sheet _ _ _ _ _
end OriginalMarkedScalarSeparableTrace318
#print axioms OriginalMarkedScalarSeparableTrace318.from_original
