module
public import OriginalPhysicalNaganoFirstJet318
public section
namespace OriginalPhysicalNaganoFourRoot318
open OriginalPhysicalNaganoJet318 OriginalPhysicalNaganoReadback318 OriginalPhysicalNaganoFirstJet318
open OriginalMarkedIntPolynomialCertificate318
variable {K : Type*} [Field K] [CharZero K]
theorem named_conic_root (a b : K) (ha : 1241*a^2=1276646) (hb : 1241*b^2=119479) :
    h ((b-15)/(a-30)) qq=0 := by
  have hn : a-30≠0 := by
    intro h
    have h' : a=30 := sub_eq_zero.mp h
    rw [h'] at ha
    norm_num at ha
  simp [h,qq,horner]
  field_simp [hn]
  linear_combination
    (79873*a^2/1241-900*a*b+7168740*a/1241+1835096*b^2/1241+
      45468120*b/1241-721563266242/1540081)*ha +
    (900*a*b-160366260*a/1241+79873*b^2/1241-
      38299380*b/1241+6406943482133/1540081)*hb

theorem root_from_original (r₀ r₁ r₃ : K)
    (h₀ : r₀^2= -14*119136) (h₁ : r₁^2= -6*(119136-32))
    (h₃ : r₃^2= -21*(119136+343)) :
    h ((8*r₃/r₀-15)/(49*r₁/r₀-30)) qq=0 := by
  apply named_conic_root
  · rw [div_pow, mul_pow, h₁, h₀]
    norm_num
  · rw [div_pow, mul_pow, h₃, h₀]
    norm_num

/-- The actual three ordinary radical signs fix a coarse point and its first jet
in the literal T parameter; no positive branch or P33 marking is smuggled in. -/
theorem from_original (r₀ r₁ r₃ : K)
    (h₀ : r₀^2= -14*119136) (h₁ : r₁^2= -6*(119136-32))
    (h₃ : r₃^2= -21*(119136+343)) :
    let z := (8*r₃/r₀-15)/(49*r₁/r₀-30)
    h z nn/h z dd=119136 ∧ h z bb/(108000*(h z aa)^3)=r z rx rxD ∧
    h z cc/(5443200000*(h z aa)^5)=r z ry ryD ∧
    ((dH z bb*h z aa-3*h z bb*dH z aa)*(h z dd)^2)/
      (108000*(h z aa)^4*(dH z nn*h z dd-h z nn*dH z dd))=r z rdx rdxD ∧
    ((dH z cc*h z aa-5*h z cc*dH z aa)*(h z dd)^2)/
      (5443200000*(h z aa)^6*(dH z nn*h z dd-h z nn*dH z dd))=r z rdy rdyD := by
  dsimp only
  have hz := root_from_original r₀ r₁ r₃ h₀ h₁ h₃
  exact ⟨physical_T _ hz,rx_eq _ hz,ry_eq _ hz,marked_jet _ hz⟩
end OriginalPhysicalNaganoFourRoot318
#print axioms OriginalPhysicalNaganoFourRoot318.from_original
