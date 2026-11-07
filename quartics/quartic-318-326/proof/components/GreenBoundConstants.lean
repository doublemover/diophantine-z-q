module
public import QuarticOptimization
public section
namespace GreenBoundConstants

/-- Numerical consequence of Bruin's supplied analytic bounds. This theorem
checks constants only; it does not assert the Green-function estimates. -/
theorem regularized_bound (N R : ℝ) (hN : 1 ≤ N)
    (hlo : -30000-(279/10000)*N-2*max 172 ((379/100)*N)-
      (4096/975)*max (257/10) ((63/5000)*N^2) ≤ R)
    (hhi : R ≤ 15800+(279/10000)*N+2*max 172 ((379/100)*N)+
      (109/1250)*N^2) : |R| < 31000*N^2 := by
  have hNs : N ≤ N^2 := by nlinarith
  have hNs1 : 1 ≤ N^2 := by nlinarith
  have hs : max (172:ℝ) ((379/100)*N) ≤ 172*N^2 := by
    apply max_le
    · nlinarith
    · nlinarith
  have hz : max (257/10:ℝ) ((63/5000)*N^2) ≤ (257/10)*N^2 := by
    apply max_le
    · nlinarith
    · nlinarith
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- Even the larger2π conversion fits this margin using only2π<8. -/
theorem scaled_bound (N R factor : ℝ) (hN : 1 ≤ N)
    (hR : |R| < 31000*N^2) (hf0 : 0 ≤ factor) (hf8 : factor ≤ 8) :
    |factor*R| < 2^20*N^2 := by
  rw [abs_mul,abs_of_nonneg hf0]
  have hs : 1 ≤ N^2 := by nlinarith
  have ha : 0 ≤ |R| := abs_nonneg R
  have hm := mul_le_mul_of_nonneg_right hf8 ha
  norm_num
  nlinarith

end GreenBoundConstants
