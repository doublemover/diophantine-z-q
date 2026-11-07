module
public import FormalDifferential318
public import Mathlib.Algebra.Polynomial.Derivation
public section
namespace FormalChain318
open PowerSeries Finsupp
variable {R σ : Type*} [CommRing R]

private theorem coeff_pow_zero (g : MvPowerSeries σ R) (hg : g.constantCoeff=0)
    (n : σ →₀ ℕ) (k : ℕ) (hk : n.degree<k) : MvPowerSeries.coeff n (g^k)=0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hk) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hg)

private theorem polynomial_chain (i : σ) (f : Polynomial R) (g : MvPowerSeries σ R)
    (hg : HasSubst g) :
    MvPowerSeries.pderiv i ((f:PowerSeries R).subst g)=
      (derivative (f:PowerSeries R)).subst g*MvPowerSeries.pderiv i g := by
  simp [subst_coe hg,derivative_coe,Derivation.comp_aeval_eq (a:=g) (MvPowerSeries.pderiv i) f,
    smul_eq_mul]

/-- Chain rule for substituting a zero-constant multivariate power series into
an arbitrary univariate power series. -/
theorem chain (i : σ) (f : PowerSeries R) (g : MvPowerSeries σ R)
    (hg0 : g.constantCoeff=0) :
    MvPowerSeries.pderiv i (f.subst g)=
      (derivative f).subst g*MvPowerSeries.pderiv i g := by
  classical
  have hg : HasSubst g := HasSubst.of_constantCoeff_zero hg0
  ext n
  let m := n.degree+2
  have hc : MvPowerSeries.coeff (n+single i 1) (f.subst g)=
      MvPowerSeries.coeff (n+single i 1) ((trunc m f:PowerSeries R).subst g) := by
    rw [coeff_subst hg,coeff_subst hg]
    refine finsum_congr fun k => ?_
    by_cases hk : k<m
    · rw [coeff_coe_trunc_of_lt hk]
    · have hz : MvPowerSeries.coeff (n+single i 1) (g^k)=0 :=
        coeff_pow_zero g hg0 _ k (by simp only [map_add,degree_single]; dsimp [m] at hk; omega)
      simp only [hz,smul_zero]
  rw [MvPowerSeries.coeff_pderiv,hc,←MvPowerSeries.coeff_pderiv,polynomial_chain i _ g hg,
    MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ⟨a,b⟩ hab => ?_
  congr 1
  simp only [coeff_subst hg,coeff_derivative,Polynomial.coeff_coe,coeff_trunc]
  refine finsum_congr fun k => ?_
  split_ifs with hk
  · rfl
  · have hab' : a+b=n := Finset.mem_antidiagonal.mp hab
    have ha : a.degree≤n.degree := by rw [←hab',map_add]; omega
    have hz : MvPowerSeries.coeff a (g^k)=0 := coeff_pow_zero g hg0 a k (by dsimp [m] at hk; omega)
    simp only [hz,smul_zero]

end FormalChain318
#print axioms FormalChain318.chain
