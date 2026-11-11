module
public import ActualTwoDescentTorsionInvolution318
public section
noncomputable section
namespace ActualTwoDescentTranslatedSquarePair318
open ActualTwoDescentTorsionTranslation318 ActualTwoDescentTorsionSquarePairs318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]

/-- Translation acts on the ACTUAL pair of Kummer coordinates by(3,-n),
with explicit nonzero multipliers over the same field. -/
theorem actual_translated_square_pair (n x y a b : K) (hn : n ≠ 0)
    (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) (H : SquarePair (x+3*n) (x-n) a b) :
    SquarePair (translatedX n x+3*n) (translatedX n x-n) (3*a) ((-n)*b) := by
  obtain ⟨r,s,hr,hs,heA,heB⟩ := H
  have hy : y ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hc
    exact (mul_ne_zero (mul_ne_zero hx hB) hA) hc.symm
  refine ⟨r*(2*n/(x+3*n)),s*(2*y/((x-n)*(x+3*n))),?_,?_,?_,?_⟩
  · exact mul_ne_zero hr (div_ne_zero (mul_ne_zero (by norm_num) hn) hA)
  · exact mul_ne_zero hs (div_ne_zero (mul_ne_zero (by norm_num) hy) (mul_ne_zero hB hA))
  · rw [translated_first_square n x hA,heA,mul_pow]
    ring
  · rw [translated_second_square n x y hB hA hc,heB,mul_pow]
    ring

/-- Replace literal representatives by square-equivalent representatives,
retaining the same actual point and multiplying its actual square roots. -/
lemma actual_pair_rescale (A B a b a' b' r s : K) (hr : r ≠ 0) (hs : s ≠ 0)
    (ha : a=a'*r^2) (hb : b=b'*s^2) (H : SquarePair A B a b) : SquarePair A B a' b' := by
  obtain ⟨u,v,hu,hv,hA,hB⟩ := H
  refine ⟨r*u,s*v,mul_ne_zero hr hu,mul_ne_zero hs hv,?_,?_⟩
  · rw [hA,ha,mul_pow]
    ring
  · rw [hB,hb,mul_pow]
    ring

end ActualTwoDescentTranslatedSquarePair318
