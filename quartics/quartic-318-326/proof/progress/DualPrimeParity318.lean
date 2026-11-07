module
public import DeltaPrime318
public section
namespace DualPrimeParity318
open ConcreteG8Domain EuclideanSqrtTwo318 FractionSqrtTwo318
set_option maxHeartbeats 0
noncomputable section

/-- The dual abscissa is even at every actual prime-multiplicity valuation
of Z[sqrt2]. No classification of split/inert prime ideals is assumed. -/
theorem dual_prime_even (q:O) (hq:Prime q) (X Y:K) (m:ℤ)
    (hX:primePlace q hq X=m) (he:Y^2=X^3+4*D*X) : Even m := by
  by_cases hd:q∣DeltaPrime318.delta
  · have hass:Associated q DeltaPrime318.delta :=
      (hq.irreducible.dvd_irreducible_iff_associated DeltaPrime318.delta_prime.irreducible).mp hd
    rw [primePlace_associated q DeltaPrime318.delta hq DeltaPrime318.delta_prime hass] at hX
    exact DeltaPrime318.dual_even X Y m hX he
  let v:=primePlace q hq
  have hdelta:v (3-i)=0 := by
    have hid:toK DeltaPrime318.delta=3-i := by
      ext <;> norm_num [toK_pair,DeltaPrime318.delta,i,pair,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
    rw [←hid]
    exact primePlace_not_dvd q hq _ hd
  have hi0:i≠0 := by intro hh; have hh':=congrArg QuadraticAlgebra.im hh; norm_num [i,pair] at hh'
  obtain ⟨n,hn⟩:=WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hi0)
  have htwo:v (2:K)=(2*n:ℤ) := by
    rw [←i_square,v.map_pow,←hn]
    norm_cast
  have hA:v (4*D)=(4*n:ℤ) := by
    have hf:(4:K)=2^2 := by norm_num
    rw [v.map_mul,hf,D,v.map_pow,v.map_pow,htwo,hdelta]
    simp only [nsmul_zero,add_zero]
    norm_cast
    simp only [two_nsmul]
    omega
  exact DualLocalArithmetic318.dual_even_of_coefficient_four v X Y (4*D) m n hX hA he

end
end DualPrimeParity318
#print axioms DualPrimeParity318.dual_prime_even
