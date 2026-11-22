module
public import ActualVendorLSGLemniscateIndepSymm318
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination
public section
noncomputable section

namespace ActualLSGUnitSquarePeriod318

open Complex LSG.Weierstrass LSG.LemniscateIndep

/-- The literal unit square lattice, with the positive imaginary period. -/
def L : PeriodPair where
  ω₁ := 1
  ω₂ := Complex.I
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro a b h
    have hC : (a:ℂ)*1+(b:ℂ)*Complex.I=0 := by
      simpa only [Complex.real_smul] using h
    exact ⟨by simpa [Complex.mul_re] using congrArg Complex.re hC,
      by simpa [Complex.mul_im] using congrArg Complex.im hC⟩

theorem period_one : L.ω₁=((1:ℝ):ℂ) := by unfold L <;> rfl
theorem period_i : L.ω₂=Complex.I*((1:ℝ):ℂ) := by unfold L; simp

private theorem no_half_im {z : ℂ} (hz : z.im=(1:ℝ)/2) : z∉L.lattice := by
  intro h
  obtain ⟨m,n,hEq⟩ := (mem_lattice_sq period_one period_i).mp h
  have hn : (n:ℝ)=z.im := by
    simpa [Complex.mul_im] using congrArg Complex.im hEq
  have hp : (0:ℝ)<(n:ℝ) := by rw [hn,hz]; norm_num
  have hq : (n:ℝ)<1 := by rw [hn,hz]; norm_num
  have hp' : (0:ℤ)<n := by exact_mod_cast hp
  have hq' : n<1 := by exact_mod_cast hq
  omega

private abbrev half : ℂ := (((1:ℝ)/2:ℝ):ℂ)

private theorem half_notMem : half∉L.lattice :=
  ofReal_notMem (by norm_num) period_one period_i (by norm_num) (by norm_num)

private theorem halfI_notMem : Complex.I*half∉L.lattice :=
  no_half_im (by norm_num [Complex.mul_im])

/-- Real first half-period abscissa. Its nonvanishing is determined by
the degree-two Weierstrass equality, not from an asymptotic estimate. -/
def e : ℝ := (L.weierstrassP half).re

theorem half_abscissa : L.weierstrassP half=(e:ℂ) :=
  weierstrassP_ofReal period_one period_i ((1:ℝ)/2)

private theorem half_abscissa_ne : L.weierstrassP half≠0 := by
  intro hz
  have he : L.weierstrassP (Complex.I*half)=L.weierstrassP half := by
    rw [weierstrassP_I_mul period_one period_i,hz,neg_zero]
  rcases (weierstrassP_eq_iff L half_notMem halfI_notMem).mp he with h|h
  · exact no_half_im (by norm_num [Complex.mul_im]) h
  · exact no_half_im (by norm_num [Complex.mul_im]) h

theorem e_ne : e≠0 := by
  intro hz
  exact half_abscissa_ne (by rw [half_abscissa,hz,Complex.ofReal_zero])

theorem g3_zero : L.g₃=0 := g₃_eq_zero_of_square period_one period_i

/-- The real square-lattice scale needs no evaluation of a beta integral:
g₂ comes from the genuine nonzero real half-period root. -/
theorem g2_eq : L.g₂=4*(e:ℂ)^2 := by
  have hp : L.ω₁/2=half := by rw [period_one,Complex.ofReal_div] <;> simp
  have hm : L.ω₁/2∉L.lattice := hp.symm ▸ half_notMem
  have h := weierstrassP_half_cubic L L.ω₁_mem_lattice hm
  rw [hp,g3_zero,sub_zero] at h
  have he : (4*(L.weierstrassP half)^2-L.g₂)*L.weierstrassP half=0 := by
    linear_combination h
  have h0 := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right half_abscissa_ne)
  rw [half_abscissa] at h0
  exact h0.symm

def fourthScale : ℝ := Real.sqrt |e|

theorem fourthScale_pos : 0<fourthScale :=
  Real.sqrt_pos.2 (abs_pos.2 e_ne)

theorem scale_matches : (fourthScale:ℂ)^4=L.g₂/4 := by
  have h2 : fourthScale^2=|e| := Real.sq_sqrt (abs_nonneg _)
  have h4 : fourthScale^4=e^2 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,h2,sq_abs]
  rw [g2_eq]
  have hC : (fourthScale:ℂ)^4=(e:ℂ)^2 := by exact_mod_cast h4
  rw [hC]
  ring

end ActualLSGUnitSquarePeriod318
