module
public import OriginalScalarExceptionalRow0318
public import OriginalScalarExceptionalRow1318
public import OriginalScalarExceptionalRow2318
public import OriginalScalarExceptionalRow3318
public import OriginalScalarExceptionalRow4318
public section
namespace OriginalScalarEffectiveChart318
open OriginalScalarProjectiveObstruction318 OriginalScalarExceptionalMap318 OriginalScalarExceptionalRows318
open OriginalMarkedIntPolynomialCertificate318
section
variable {K : Type*} [Field K] [CharZero K]
theorem chart_from_conic (a b : K) (x : ℚ) (hab : a^2+b^2=1125)
    (ha : 119136*(x:K)^2*a^2=1029*(119136*(x:K)^2)-32928) :
    let z := (b-15)/(a-30)
    a-30≠0 ∧ 1+z^2≠0 ∧ horner z dd≠0 ∧ horner z nn=(x:K)^2*horner z vv := by
  dsimp only
  have hrat : (-343:ℚ)+x^2*160089 ≠ 0 := by
    simpa [g2,horner] using no_rat_square 5 (by decide) _ proj2 x
  have hratK : (-343:K)+(x:K)^2*160089 ≠ 0 := by exact_mod_cast hrat
  have hd : a-30≠0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [he] at ha
    apply hratK
    linear_combination (-1/96)*ha
  let z := (b-15)/(a-30)
  have c : a*(1+z^2)=30*(z^2-z-1) := by
    dsimp [z]; field_simp [hd]; linear_combination (a-30)*hab
  have he : 1+z^2≠0 := by
    intro h
    have hr : z= -2 := by linear_combination (1/30)*c - ((a-30)/30)*h
    rw [hr] at h
    norm_num at h
  have nt : horner z nn=(x:K)^2*horner z vv := by
    calc
      horner z nn = 10976*(1+z^2)^2 := by simp [nn,horner]; ring
      _ = 119136*(x:K)^2*(343*(1+z^2)^2-300*(z^2-z-1)^2) := by
        linear_combination ((1+z^2)^2/3)*ha - (119136*(x:K)^2/3)*(a*(1+z^2)+30*(z^2-z-1))*c
      _ = (x:K)^2*horner z vv := by simp [vv,horner]; ring
  have hdT : horner z dd≠0 := by
    intro h
    rw [vv_eq,h,mul_zero,mul_zero] at nt
    have hz : horner z nn=10976*(1+z^2)^2 := by simp [nn,horner]; ring
    exact (mul_ne_zero (by norm_num) (pow_ne_zero _ he)) (hz.symm.trans nt)
  exact ⟨hd,he,hdT,nt⟩

theorem conic_of_roots (r₀ r₁ r₃ : K) (x : ℚ) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2))
    (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₃ : r₃^2= -21*(119136*(x:K)^2+343)) :
    (49*r₁/r₀)^2+(8*r₃/r₀)^2=1125 ∧
    119136*(x:K)^2*(49*r₁/r₀)^2=1029*(119136*(x:K)^2)-32928 := by
  have hx' : (x:K)≠0 := by exact_mod_cast hx
  constructor
  · rw [div_pow,div_pow,mul_pow,mul_pow,h₁,h₃,h₀]
    field_simp [hx']; ring
  · rw [div_pow,mul_pow,h₁,h₀]
    field_simp [hx']; ring
end
@[expose] def finiteExceptions : List (List ℤ) := [f1,f2,f3,f4,f5,f6,f7,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19,f20,f21,f22,f23,f24,f25]
/-- The literal three root equations produce the ordinary signed conic chart and exclude
every normalized HZ210/EK/Mestre exceptional factor at all original rational scalar points. -/
theorem from_original {K : Type*} [Field K] [CharZero K] (r₀ r₁ r₃ : K) (x : ℚ) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₃ : r₃^2= -21*(119136*(x:K)^2+343)) :
    let z := (8*r₃/r₀-15)/(49*r₁/r₀-30)
    49*r₁/r₀-30≠0 ∧ 1+z^2≠0 ∧ horner z dd≠0 ∧ horner z nn=(x:K)^2*horner z vv ∧
    ∀ f ∈ finiteExceptions, horner z f≠0 := by
  dsimp only
  have h := conic_of_roots r₀ r₁ r₃ x hx h₀ h₁ h₃
  obtain ⟨hc,he,hd,hz⟩ := chart_from_conic _ _ x h.1 h.2
  refine ⟨hc,he,hd,hz,?_⟩
  intro f hf
  simp only [finiteExceptions,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nz1 _ x hd hz
  · exact nz2 _ x hd hz
  · exact nz3 _ x hd hz
  · exact nz4 _ x hd hz
  · exact nz5 _ x hd hz
  · exact nz6 _ x hd hz
  · exact nz7 _ x hd hz
  · exact nz9 _ x hd hz
  · exact nz10 _ x hd hz
  · exact nz11 _ x hd hz
  · exact nz12 _ x hd hz
  · exact nz13 _ x hd hz
  · exact nz14 _ x hd hz
  · exact nz15 _ x hd hz
  · exact nz16 _ x hd hz
  · exact nz17 _ x hd hz
  · exact nz18 _ x hd hz
  · exact nz19 _ x hd hz
  · exact nz20 _ x hd hz
  · exact nz21 _ x hd hz
  · exact nz22 _ x hd hz
  · exact nz23 _ x hd hz
  · exact nz24 _ x hd hz
  · exact nz25 _ x hd hz
end OriginalScalarEffectiveChart318
#print axioms OriginalScalarEffectiveChart318.from_original
