module
public import OriginalPhysicalNaganoJet318
public section
namespace OriginalPhysicalNaganoReadback318
open OriginalMarkedIntPolynomialCertificate318 OriginalPhysicalNaganoJet318
set_option maxRecDepth 16384
set_option maxHeartbeats 1400000
variable {K : Type*} [Field K] [CharZero K]
@[expose] def h (z : K) (l : List ℤ) : K := horner z l
@[expose] def r (z : K) (l : List ℤ) (d : ℕ) : K := h z l / d
@[expose] def W (z : K) : K := h z np * h z dd - h z nn * h z dp
theorem nonzero_aa (z : K) (hz : h z qq=0) : h z aa ≠ 0 := by
  have mv := vanish z hz .aaunit
  simp only [row, Ev] at mv
  have he : h z aa * h z aaInv = ((aaU:ℕ):K) := by
    
    unfold h aaU
    norm_num only [horner, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Int.cast_zero, mul_zero, add_zero] at mv
    linear_combination mv
  intro hn
  rw [hn,zero_mul] at he
  exact (show ((aaU:ℕ):K) ≠ 0 by exact_mod_cast (show aaU ≠ 0 by decide)) he.symm

theorem nonzero_dd (z : K) (hz : h z qq=0) : h z dd ≠ 0 := by
  have mv := vanish z hz .ddunit
  simp only [row, Ev] at mv
  have he : h z dd * h z ddInv = ((ddU:ℕ):K) := by
    
    unfold h ddU
    norm_num only [horner, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Int.cast_zero, mul_zero, add_zero] at mv
    linear_combination mv
  intro hn
  rw [hn,zero_mul] at he
  exact (show ((ddU:ℕ):K) ≠ 0 by exact_mod_cast (show ddU ≠ 0 by decide)) he.symm

theorem nonzero_jac (z : K) (hz : h z qq=0) : W z ≠ 0 := by
  have mv := vanish z hz .jacunit
  simp only [row, jac, Ev] at mv
  have he : W z * h z jacInv = ((jacU:ℕ):K) := by
    unfold W
    unfold h jacU
    norm_num only [horner, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Int.cast_zero, mul_zero, add_zero] at mv
    linear_combination mv
  intro hn
  rw [hn,zero_mul] at he
  exact (show ((jacU:ℕ):K) ≠ 0 by exact_mod_cast (show jacU ≠ 0 by decide)) he.symm

theorem physical_T (z : K) (hz : h z qq=0) : h z nn / h z dd = 119136 := by
  have mv := vanish z hz .coordinate
  simp only [row,Ev] at mv
  norm_num only [Int.cast_neg,Int.cast_one,Int.cast_ofNat] at mv
  apply (div_eq_iff (nonzero_dd z hz)).mpr
  unfold h
  linear_combination mv

theorem rx_eq (z : K) (hz : h z qq=0) : (h z bb) / (108000*(h z aa)^3) = r z rx rxD := by
  have ha := nonzero_aa z hz
  have hd := nonzero_dd z hz
  have hw := nonzero_jac z hz
  have dn : ((rxD:ℕ):K) ≠ 0 := by exact_mod_cast (show rxD ≠ 0 by decide)
  have hc : (108000*(h z aa)^3:K) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ ha)
  apply (div_eq_div_iff hc dn).mpr
  have mv := vanish z hz .rx
  simp only [row, Ev] at mv
  change (h z bb)*((rxD:ℕ):K) = h z rx * (108000*(h z aa)^3) 
  
  unfold h
  norm_num only [Int.reduceNeg,Int.cast_neg,Int.cast_one,Int.cast_ofNat] at mv
  unfold rxD
  linear_combination mv

theorem ry_eq (z : K) (hz : h z qq=0) : (h z cc) / (5443200000*(h z aa)^5) = r z ry ryD := by
  have ha := nonzero_aa z hz
  have hd := nonzero_dd z hz
  have hw := nonzero_jac z hz
  have dn : ((ryD:ℕ):K) ≠ 0 := by exact_mod_cast (show ryD ≠ 0 by decide)
  have hc : (5443200000*(h z aa)^5:K) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ ha)
  apply (div_eq_div_iff hc dn).mpr
  have mv := vanish z hz .ry
  simp only [row, Ev] at mv
  change (h z cc)*((ryD:ℕ):K) = h z ry * (5443200000*(h z aa)^5) 
  
  unfold h
  norm_num only [Int.reduceNeg,Int.cast_neg,Int.cast_one,Int.cast_ofNat] at mv
  unfold ryD
  linear_combination mv

theorem rt_eq (z : K) (hz : h z qq=0) : (W z) / ((h z dd)^2) = r z rt rtD := by
  have ha := nonzero_aa z hz
  have hd := nonzero_dd z hz
  have hw := nonzero_jac z hz
  have dn : ((rtD:ℕ):K) ≠ 0 := by exact_mod_cast (show rtD ≠ 0 by decide)
  have hc : ((h z dd)^2:K) ≠ 0 := by
    exact pow_ne_zero _ hd
  apply (div_eq_div_iff hc dn).mpr
  have mv := vanish z hz .rt
  simp only [row, jac, Ev] at mv
  change (W z)*((rtD:ℕ):K) = h z rt * ((h z dd)^2) 
  unfold W
  unfold h
  norm_num only [Int.reduceNeg,Int.cast_neg,Int.cast_one,Int.cast_ofNat] at mv
  unfold rtD
  linear_combination mv

theorem rz_eq (z : K) (hz : h z qq=0) : ((h z dd)^2) / (W z) = r z rz rzD := by
  have ha := nonzero_aa z hz
  have hd := nonzero_dd z hz
  have hw := nonzero_jac z hz
  have dn : ((rzD:ℕ):K) ≠ 0 := by exact_mod_cast (show rzD ≠ 0 by decide)
  have hc : (W z:K) ≠ 0 := by
    exact hw
  apply (div_eq_div_iff hc dn).mpr
  have mv := vanish z hz .rz
  simp only [row, jac, Ev] at mv
  change ((h z dd)^2)*((rzD:ℕ):K) = h z rz * (W z) 
  unfold W
  unfold h
  norm_num only [Int.reduceNeg,Int.cast_neg,Int.cast_one,Int.cast_ofNat] at mv
  unfold rzD
  linear_combination mv

theorem rdx_eq (z : K) (hz : h z qq=0) : (((h z bp)*(h z aa)-3*(h z bb)*(h z ap))*(h z dd)^2) / (108000*(h z aa)^4*W z) = r z rdx rdxD := by
  have ha := nonzero_aa z hz
  have hd := nonzero_dd z hz
  have hw := nonzero_jac z hz
  have dn : ((rdxD:ℕ):K) ≠ 0 := by exact_mod_cast (show rdxD ≠ 0 by decide)
  have hc : (108000*(h z aa)^4*W z:K) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hw
  apply (div_eq_div_iff hc dn).mpr
  have mv := vanish z hz .rdx
  simp only [row, jac, Ev] at mv
  change (((h z bp)*(h z aa)-3*(h z bb)*(h z ap))*(h z dd)^2)*((rdxD:ℕ):K) = h z rdx * (108000*(h z aa)^4*W z) 
  unfold W
  unfold h
  norm_num only [Int.reduceNeg,Int.cast_neg,Int.cast_one,Int.cast_ofNat] at mv
  unfold rdxD
  linear_combination mv

theorem rdy_eq (z : K) (hz : h z qq=0) : (((h z cp)*(h z aa)-5*(h z cc)*(h z ap))*(h z dd)^2) / (5443200000*(h z aa)^6*W z) = r z rdy rdyD := by
  have ha := nonzero_aa z hz
  have hd := nonzero_dd z hz
  have hw := nonzero_jac z hz
  have dn : ((rdyD:ℕ):K) ≠ 0 := by exact_mod_cast (show rdyD ≠ 0 by decide)
  have hc : (5443200000*(h z aa)^6*W z:K) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hw
  apply (div_eq_div_iff hc dn).mpr
  have mv := vanish z hz .rdy
  simp only [row, jac, Ev] at mv
  change (((h z cp)*(h z aa)-5*(h z cc)*(h z ap))*(h z dd)^2)*((rdyD:ℕ):K) = h z rdy * (5443200000*(h z aa)^6*W z) 
  unfold W
  unfold h
  norm_num only [Int.reduceNeg,Int.cast_neg,Int.cast_one,Int.cast_ofNat] at mv
  unfold rdyD
  linear_combination mv
end OriginalPhysicalNaganoReadback318
#print axioms OriginalPhysicalNaganoReadback318.rx_eq
#print axioms OriginalPhysicalNaganoReadback318.ry_eq
#print axioms OriginalPhysicalNaganoReadback318.rt_eq
#print axioms OriginalPhysicalNaganoReadback318.rz_eq
#print axioms OriginalPhysicalNaganoReadback318.rdx_eq
#print axioms OriginalPhysicalNaganoReadback318.rdy_eq
