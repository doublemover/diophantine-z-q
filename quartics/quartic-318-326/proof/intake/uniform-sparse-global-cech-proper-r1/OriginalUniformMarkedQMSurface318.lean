module
public import OriginalUniformCowanUnits318
public import OriginalUniformCowanDerivative318
public import OriginalUniformSparseJet318
public import OriginalUniformCowanReadNN318
public import OriginalUniformCowanReadMM318
public import OriginalUniformCowanReadJJ318
public import OriginalUniformCowanReadRM318
public section
namespace OriginalUniformMarkedQMSurface318
open OriginalUniformCowanData318 OriginalUniformFractionCert318 OriginalMarkedIntPolynomialCertificate318 OriginalUniformCowanRead318 OriginalUniformSparseJet318 OriginalUniformCowanLaws318
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
variable {K : Type*} [Field K]
structure Row (K : Type*) where
  m : K
  n : K
  p : K
  q : K
  h : K
  a : K
  b : K
  T : K
  AA : K
  BB : K
  CC : K
  J : K
  X : K
  Y : K
@[expose] def row (z : K) : Row K := ⟨OriginalUniformCowanData318.read z regm,OriginalUniformCowanData318.read z regn,OriginalUniformCowanData318.read z regp,OriginalUniformCowanData318.read z regq,OriginalUniformCowanData318.read z regh,OriginalUniformCowanData318.read z rega,OriginalUniformCowanData318.read z regb,OriginalUniformCowanData318.read z regT,OriginalUniformCowanData318.read z regAA,OriginalUniformCowanData318.read z regBB,OriginalUniformCowanData318.read z regCC,OriginalUniformCowanData318.read z regJ,OriginalUniformCowanData318.read z regX,OriginalUniformCowanData318.read z regY⟩
@[expose] def discRoot (d : Row K) (v r₂ : K) : K := -v*r₂*d.h
@[expose] def qCoeff (d : Row K) (r₀ R : K) : K := r₀*(d.a+d.b*R)
@[expose] def normalizedKS (d : Row K) (R : K) : K :=
  2*detNumerator d.m d.n d.p d.q R/(d.J*(d.m^2-d.n)*d.n*OriginalUniformSparseJet318.delta d.m d.n)
structure Laws (d : Row K) : Prop where
  eqNN : lawNN d.n d.AA d.BB d.CC=0
  eqMM : lawMM d.m d.n d.BB d.CC=0
  eqJJ : lawJJ d.AA d.BB d.CC d.J=0
  eqRM : lawRM d.m d.n d.h d.T=0
  eqQ0 : lawQ0 d.m d.n d.p d.q d.a d.b d.T=0
  eqQ1 : lawQ1 d.m d.n d.p d.q d.a d.b d.T=0
  eqKS : lawKS d.m d.n d.p d.q d.J d.X d.Y=0
  nzN : d.n≠0
  nzGap : d.n-5≠0
  nzSplit : d.m^2-d.n≠0
  nzNorm : d.a^2-d.b^2*(d.m^2-d.n)≠0
  nzE : (d.n^2-5*d.n)*(2*d.m)+10*d.n^2-90*d.n+216≠0
  nzJ : d.J≠0
  nzX : d.X≠0
  nzY : d.Y≠0
  nzBB : d.BB≠0
  nzCC : d.CC≠0
theorem laws_at [CharZero K] (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0)
    (hf : ∀ i,horner z (OriginalScalarNamedUnits318.factor i)≠0) : Laws (row z) := by
  constructor
  · apply asNN
    intro v hv
    simp only [NNVars,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hd .regn
    · exact hd .regAA
    · exact hd .regBB
    · exact hd .regCC
  · apply asMM
    intro v hv
    simp only [MMVars,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hd .regm
    · exact hd .regn
    · exact hd .regBB
    · exact hd .regCC
  · apply asJJ
    intro v hv
    simp only [JJVars,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hd .regAA
    · exact hd .regBB
    · exact hd .regCC
    · exact hd .regJ
  · apply asRM
    intro v hv
    simp only [RMVars,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hd .regm
    · exact hd .regn
    · exact hd .regh
    · exact hd .regT
  · apply asQ0
    intro v hv
    simp only [Q0Vars,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hd .regm
    · exact hd .regn
    · exact hd .regp
    · exact hd .regq
    · exact hd .rega
    · exact hd .regb
    · exact hd .regT
  · apply asQ1
    intro v hv
    simp only [Q1Vars,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hd .regm
    · exact hd .regn
    · exact hd .regp
    · exact hd .regq
    · exact hd .rega
    · exact hd .regb
    · exact hd .regT
  · apply asKS
    intro v hv
    simp only [KSVars,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hd .regm
    · exact hd .regn
    · exact hd .regp
    · exact hd .regq
    · exact hd .regJ
    · exact hd .regX
    · exact hd .regY
  · exact OriginalUniformCowanUnits318.nzN z hd hf
  · exact OriginalUniformCowanUnits318.nzGap z hd hf
  · exact OriginalUniformCowanUnits318.nzSplit z hd hf
  · exact OriginalUniformCowanUnits318.nzNorm z hd hf
  · exact OriginalUniformCowanUnits318.nzE z hd hf
  · exact OriginalUniformCowanUnits318.nzJ z hd hf
  · exact OriginalUniformCowanUnits318.nzX z hd hf
  · exact OriginalUniformCowanUnits318.nzY z hd hf
  · exact OriginalUniformCowanUnits318.nzBB z hd hf
  · exact OriginalUniformCowanUnits318.nzCC z hd hf
structure Sheet (d : Row K) (R u : K) : Prop where
  root_eq : R^2=d.m^2-d.n
  root_ne : R≠0
  s_ne : d.m+R≠0
  t_ne : d.m-R≠0
  st : (d.m+R)*(d.m-R)=d.n
  u_ne : u≠0
  self_adjoint : u^2*V0 d.m d.p d.q R=42*V2 d.m d.p d.q R
  evalKS : normalizedKS d R = -10080/(d.X*d.Y)
theorem make_sheet [CharZero K] (d : Row K) (h : Laws d) (v r₀ r₂ : K)
    (hv : v^2=5) (h₀ : r₀^2= -14*d.T) (h₂ : r₂^2=42*(d.T-76832)) (hn₀ : r₀≠0) :
    Sheet d (discRoot d v r₂) (qCoeff d r₀ (discRoot d v r₂)) := by
  let R := discRoot d v r₂
  have hr : R^2=d.m^2-d.n := by
    have he := h.eqRM
    unfold lawRM at he
    change (-v*r₂*d.h)^2=_
    rw [mul_pow,mul_pow,neg_sq,hv,h₂]
    linear_combination -he
  have st : (d.m+R)*(d.m-R)=d.n := by linear_combination -hr
  have nst := h.nzN
  rw [←st] at nst
  have hn := h.nzNorm
  have hconj : (d.a+d.b*R)*(d.a-d.b*R) = d.a^2-d.b^2*(d.m^2-d.n) := by
    linear_combination -d.b^2*hr
  rw [←hconj] at hn
  have hU : qCoeff d r₀ R≠0 := mul_ne_zero hn₀ (left_ne_zero_of_mul hn)
  have hD : OriginalUniformSparseJet318.delta d.m d.n≠0 := mul_ne_zero h.nzGap (pow_ne_zero _ h.nzE)
  have hJ := h.nzJ
  have hnZ := h.nzN
  have hΔ := h.nzSplit
  have hF := mul_ne_zero h.nzX h.nzY
  have he := quaternion_remainder d.m d.n d.p d.q d.a d.b d.T R hr
  rw [h.eqQ0,h.eqQ1] at he
  have hk := ks_remainder d.m d.n d.p d.q d.J d.X d.Y R hr
  rw [h.eqKS] at hk
  refine ⟨hr,?_,left_ne_zero_of_mul nst,right_ne_zero_of_mul nst,st,hU,?_,?_⟩
  · change R≠0
    intro hh; apply hΔ; rw [←hr,hh]; norm_num
  · change (r₀*(d.a+d.b*R))^2*V0 d.m d.p d.q R=_
    rw [mul_pow,h₀]
    linear_combination he
  · unfold normalizedKS
    apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hJ hΔ) hnZ) hD) hF).mpr
    linear_combination 2*hk
@[expose] def zCoord (r₀ r₁ r₃ : K) : K := (8*r₃/r₀-15)/(49*r₁/r₀-30)
structure Physical (x : ℚ) (r₀ r₁ r₂ r₃ v : K) [CharZero K] : Prop where
  trueT : (row (zCoord r₀ r₁ r₃)).T=119136*(x:K)^2
  actual_laws : Laws (row (zCoord r₀ r₁ r₃))
  m_derivative : (row (zCoord r₀ r₁ r₃)).p=OriginalUniformCowanDerivative318.quotientJet (zCoord r₀ r₁ r₃) regmNum regmDen
  n_derivative : (row (zCoord r₀ r₁ r₃)).q=OriginalUniformCowanDerivative318.quotientJet (zCoord r₀ r₁ r₃) regnNum regnDen
  marked : let d := row (zCoord r₀ r₁ r₃); let R := discRoot d v r₂; Sheet d R (qCoeff d r₀ R)
/-- Every nonzero rational scalar on the original four labelled radicals.
No auxiliary denominator, Kummer root, matrix coefficient, or nonvanishing premise. -/
theorem from_original [CharZero K] (x : ℚ) (r₀ r₁ r₂ r₃ v : K) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₂ : r₂^2=42*(119136*(x:K)^2-76832)) (h₃ : r₃^2= -21*(119136*(x:K)^2+343))
    (hv : v^2=5) : Physical x r₀ r₁ r₂ r₃ v := by
  let z := zCoord r₀ r₁ r₃
  have hd := OriginalScalarCowanRegisters318.at_original r₀ r₁ r₃ x hx h₀ h₁ h₃
  obtain ⟨_,hu,hy,hz,hs⟩ := OriginalScalarEffectiveChart318.from_original r₀ r₁ r₃ x hx h₀ h₁ h₃
  change horner z OriginalScalarExceptionalMap318.nn=(x:K)^2*horner z OriginalScalarExceptionalMap318.vv at hz
  change horner z OriginalScalarExceptionalMap318.dd≠0 at hy
  have hh : (row z).T=119136*(x:K)^2 := by
    change horner _ OriginalScalarExceptionalMap318.nn / horner _ OriginalScalarExceptionalMap318.dd=_
    apply (div_eq_iff hy).mpr
    rw [hz,OriginalScalarExceptionalMap318.vv_eq]
    ring
  have hl := laws_at z hd (OriginalScalarNamedUnits318.every_factor _ hu hy hs)
  have hnr : r₀≠0 := by
    have nh := (mul_ne_zero (by norm_num : (-14:K)≠0) (mul_ne_zero (by norm_num : (119136:K)≠0) (pow_ne_zero 2 (by exact_mod_cast hx : (x:K)≠0))))
    rw [←h₀] at nh
    exact fun he => nh (by rw [he]; norm_num)
  refine ⟨hh,hl,OriginalUniformCowanDerivative318.m_jet z (hd .regm) (hd .regp),
    OriginalUniformCowanDerivative318.n_jet z (hd .regn) (hd .regq),?_⟩
  exact make_sheet (row z) hl v r₀ r₂ hv (hh.symm ▸ h₀) (hh.symm ▸ h₂) hnr
end OriginalUniformMarkedQMSurface318
#print axioms OriginalUniformMarkedQMSurface318.from_original
