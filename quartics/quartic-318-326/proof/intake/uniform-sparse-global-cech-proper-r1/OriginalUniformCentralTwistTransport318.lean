module
public import OriginalUniformOriginalTGauge318
public import OriginalSeparableSexticJet318
public import OriginalUniformSparseIgusa318
public section
noncomputable section
namespace OriginalUniformCentralTwistTransport318
open Polynomial OriginalUniformMarkedQMSurface318 OriginalUniformSparseJet318 OriginalSeparableSexticJet318
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]
/-- Relative first jet of the central twist by a unit b. The logarithmic derivative
is free: no constancy of b and no square root of b are used. -/
@[expose] def twist (J : Data K) (b l : K) (hb : b≠0) : Data K where
  F := C b*J.F
  G := C b*(J.G+C l*J.F)
  degree := by rw [natDegree_C_mul hb,J.degree]
  jet_degree := by
    apply (natDegree_C_mul_le ..).trans
    exact natDegree_add_le_of_degree_le J.jet_degree ((natDegree_C_mul_le ..).trans J.degree.le)
  inverse := C b⁻¹*J.inverse
  inverse_quotient := C b⁻¹*J.inverse_quotient
  inverse_relation := by
    rw [derivative_C_mul]
    have h : C b⁻¹*C b=(1:K[X]) := by rw [← map_mul,inv_mul_cancel₀ hb,map_one]
    calc
      _ = (C b⁻¹*C b)*(J.inverse*J.F.derivative)-1 := by ring
      _ = J.F*J.inverse_quotient := by rw [h,one_mul,J.inverse_relation]
      _ = _ := by linear_combination -(J.F*J.inverse_quotient)*h
  remainder := J.remainder
  small := J.small
  relation := by
    intro i
    obtain ⟨Q,hQ⟩ := J.relation i
    refine ⟨Q+X^(i:ℕ)*C l,?_⟩
    rw [derivative_C_mul]
    linear_combination C b * hQ

@[expose] def moment (J : Data K) (i : Fin 3) := -2*((J.remainder i).coeff 5/J.F.leadingCoeff)
@[expose] def detMoment (J : Data K) := moment J 0*moment J 2-(moment J 1)^2
theorem scaled_moment (J : Data K) (b l : K) (hb : b≠0) (i : Fin 3) :
    moment (twist J b l hb) i=moment J i / b := by
  change -2*((J.remainder i).coeff 5/(C b*J.F).leadingCoeff)=_
  rw [leadingCoeff_mul,leadingCoeff_C]
  unfold moment
  ring
theorem scaled_det (J : Data K) (b l : K) (hb : b≠0) :
    detMoment (twist J b l hb)=detMoment J/b^2 := by
  unfold detMoment
  simp only [scaled_moment]
  ring
@[expose] def rawI2 (F : K[X]) : K := -120*OriginalUniformSparseIgusa318.trans 6 6 6 F.coeff F.coeff 0
theorem weighted_i2 (F : K[X]) (b : K) : rawI2 (C b*F)=b^2*rawI2 F := by
  have hh (l : List (ℕ×ℕ×ℤ)) : l.foldr (fun a acc => ((a.2.2:ℤ):K)*(b*F.coeff a.1)*(b*F.coeff a.2.1)+acc) 0=
      b^2*l.foldr (fun a acc => ((a.2.2:ℤ):K)*F.coeff a.1*F.coeff a.2.1+acc) 0 := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.foldr_cons,ih]; ring
  simp only [rawI2,OriginalUniformSparseIgusa318.trans,coeff_C_mul,hh]
  ring
/-- Frame normalization is unchanged even for a varying central twist, over the
actual coefficient field; compare literal raw transvectants and degree-five residues. -/
theorem normalized_transport (J : Data K) (b l scale : K) (hb : b≠0) :
    rawI2 (twist J b l hb).F/scale*detMoment (twist J b l hb)=rawI2 J.F/scale*detMoment J := by
  change rawI2 (C b*J.F)/scale*detMoment (twist J b l hb)=_
  rw [weighted_i2,scaled_det]
  field_simp

/-- Direct dehomogeneous-chart nonvanishing of the first transvectant comes
from the already proved nonzero determinant, not a claim on arbitrary sparse sextics. -/
theorem actual_i2_ne [CharZero K] (d : Row K) (h : Laws d) (R u : K) (sh : Sheet d R u) :
    OriginalUniformSparseIgusa318.i2 (d.m+R) (d.m-R)≠0 := by
  have hk := sh.evalKS
  have hKS : normalizedKS d R≠0 := hk ▸ div_ne_zero (by norm_num) (mul_ne_zero h.nzX h.nzY)
  have hN : detNumerator d.m d.n d.p d.q R≠0 := by
    intro hh
    apply hKS
    simp [normalizedKS,hh]
  have h23 : 2*d.n-3≠0 := left_ne_zero_of_mul hN
  have hi := (OriginalUniformSparseIgusa318.reads_factored (d.m+R) (d.m-R)).1
  rw [hi,sh.st]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h23) (pow_ne_zero 2 h.nzN)) (pow_ne_zero 2 h.nzGap)
end OriginalUniformCentralTwistTransport318
#print axioms OriginalUniformCentralTwistTransport318.normalized_transport
#print axioms OriginalUniformCentralTwistTransport318.actual_i2_ne
