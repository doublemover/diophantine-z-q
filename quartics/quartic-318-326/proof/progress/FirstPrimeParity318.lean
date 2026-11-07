module
public import UnitSquareclasses318
public section
namespace FirstPrimeParity318
open ConcreteG8Domain EuclideanSqrtTwo318 FractionSqrtTwo318 LocalGenerator318
set_option maxHeartbeats 0
noncomputable section

@[expose] def EvenAtAllPrimes (x:K) : Prop :=
  ∀(q:O)(hq:Prime q)(m:ℤ),primePlace q hq x=m → Even m

theorem delta_unit (q:O) (hq:Prime q) (hd:¬q∣DeltaPrime318.delta) :
    primePlace q hq (3-i)=0 := by
  have hid:toK DeltaPrime318.delta=3-i := by
    ext <;> norm_num [toK_pair,DeltaPrime318.delta,i,pair,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
  rw [←hid]
  exact primePlace_not_dvd q hq _ hd

/-- The first descent allows an odd prime value only at delta. -/
theorem away_delta_even (q:O) (hq:Prime q) (hd:¬q∣DeltaPrime318.delta)
    (X Y:K) (m:ℤ) (hX:primePlace q hq X=m) (he:Y^2=X^3-D*X) : Even m := by
  let v:=primePlace q hq
  have hdelta:v (3-i)=0:=delta_unit q hq hd
  apply DualLocalArithmetic318.dual_even_of_coefficient_four v X Y (-D) m 0 hX
  · rw [v.map_neg,D,v.map_pow,hdelta]
    norm_num
  · linear_combination he

/-- Removing either no factor or exactly one delta makes every actual
prime value even. This uses all prime multiplicity valuations of the
proved Euclidean order, not an assumed place classification. -/
theorem even_adjustment (X Y:K) (hx:X≠0) (he:Y^2=X^3-D*X) :
    EvenAtAllPrimes X ∨ EvenAtAllPrimes (X/(3-i)) := by
  obtain ⟨m,hm⟩:=WithTop.ne_top_iff_exists.mp ((DeltaPrime318.place.ne_top_iff).mpr hx)
  rcases Int.even_or_odd m with hmEven|hmOdd
  · left
    intro q hq n hn
    by_cases hd:q∣DeltaPrime318.delta
    · have hass:Associated q DeltaPrime318.delta :=
        (hq.irreducible.dvd_irreducible_iff_associated DeltaPrime318.delta_prime.irreducible).mp hd
      rw [primePlace_associated q DeltaPrime318.delta hq DeltaPrime318.delta_prime hass] at hn
      change DeltaPrime318.place X=(n:ℤ) at hn
      have hmn:m=n := by exact_mod_cast hm.trans hn
      simpa [←hmn] using hmEven
    · exact away_delta_even q hq hd X Y n hn he
  · right
    intro q hq n hn
    by_cases hd:q∣DeltaPrime318.delta
    · have hass:Associated q DeltaPrime318.delta :=
        (hq.irreducible.dvd_irreducible_iff_associated DeltaPrime318.delta_prime.irreducible).mp hd
      rw [primePlace_associated q DeltaPrime318.delta hq DeltaPrime318.delta_prime hass] at hn
      change DeltaPrime318.place (X/(3-i))=(n:ℤ) at hn
      rw [DeltaPrime318.place.map_div,←hm,DeltaPrime318.value_delta] at hn
      have hmn:m-1=n := by exact_mod_cast hn
      rw [←hmn]
      exact hmOdd.sub_odd (by decide)
    · rw [(primePlace q hq).map_div,delta_unit q hq hd,sub_zero] at hn
      exact away_delta_even q hq hd X Y n hn he

end
end FirstPrimeParity318
#print axioms FirstPrimeParity318.even_adjustment
