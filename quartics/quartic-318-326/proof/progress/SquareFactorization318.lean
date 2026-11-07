module
public import FractionSqrtTwo318
public section
namespace SquareFactorization318
open ConcreteG8Domain EuclideanSqrtTwo318 FractionSqrtTwo318 UniqueFactorizationMonoid
open scoped BigOperators
set_option maxHeartbeats 0
noncomputable section

/-- Even multiplicities in the actual Euclidean order give a square times
one actual unit. -/
theorem integral_square_unit (a:O) (ha:a≠0)
    (he:∀q:O,Prime q → Even (multiplicity q a)) :
    ∃(r:O)(u:Oˣ),r^2*(u:O)=a := by
  classical
  letI : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s:=normalizedFactors a
  have hc:∀q∈s,Even (s.count q) := by
    intro q hq
    have hp:=prime_of_normalized_factor q hq
    have hh:=he q hp
    rw [multiplicity_eq_count_normalizedFactors hp.irreducible ha,
      normalize_normalized_factor q hq] at hh
    exact hh
  let r:O:=∏q∈s.toFinset,q^(s.count q/2)
  have hr:r^2=s.prod := by
    dsimp only [r]
    have hp:(∏q∈s.toFinset,q^(s.count q/2))^2=∏q∈s.toFinset,q^(s.count q) := by
      rw [←Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro q hq
      rw [←pow_mul]
      congr 1
      have hh:=hc q (Multiset.mem_toFinset.mp hq)
      obtain ⟨n,hn⟩:=hh
      omega
    have hh:(∏q∈s.toFinset,q^(s.count q))=s.prod := by
      calc
        _=(∑q∈s.toFinset,s.count q • ({q}:Multiset O)).prod := by
          simp only [Multiset.prod_sum,Multiset.prod_nsmul,Multiset.prod_singleton]
        _=s.prod := by rw [Multiset.toFinset_sum_count_nsmul_eq]
    exact hp.trans hh
  obtain ⟨u,hu⟩:=prod_normalizedFactors ha
  exact ⟨r,u,by rw [hr]; exact hu⟩

/-- For a nonzero fraction with even value at every actual prime place,
a reduced numerator and denominator both have even multiplicities. -/
theorem reduced_even_multiplicity (x:K) (hx:x≠0)
    (hv:∀(q:O)(hq:Prime q)(m:ℤ),primePlace q hq x=m → Even m) :
    ∃a b:O,a≠0 ∧ b≠0 ∧ (∀q:O,Prime q → Even (multiplicity q a)) ∧
      (∀q:O,Prime q → Even (multiplicity q b)) ∧ x=toK a/toK b := by
  obtain ⟨a,b,hab,hf⟩:=IsFractionRing.exists_reduced_fraction O x
  rw [IsFractionRing.mk'_eq_div] at hf
  change toK a/toK b=x at hf
  have hb:(b:O)≠0:=mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have ha:a≠0 := by intro hh; rw [hh,map_zero,zero_div] at hf; exact hx hf.symm
  have hboth:∀q:O,Prime q → Even (multiplicity q a) ∧ Even (multiplicity q b) := by
    intro q hq
    have he:primePlace q hq x=((multiplicity q a:ℤ)-(multiplicity q b:ℤ):ℤ) := by
      rw [←hf,(primePlace q hq).map_div,primePlace_multiplicity q hq a ha,
        primePlace_multiplicity q hq b hb]
      norm_cast
    have hh:=hv q hq _ he
    by_cases hqa:q∣a
    · have hqb:¬q∣(b:O) := fun hqb=>hq.not_isUnit (hab hqa hqb)
      have hz:=multiplicity_eq_zero_of_not_dvd hqb
      rw [hz] at hh ⊢
      norm_num at hh ⊢
      exact_mod_cast hh
    · have hz:=multiplicity_eq_zero_of_not_dvd hqa
      rw [hz] at hh ⊢
      norm_num at hh ⊢
      exact_mod_cast hh
  exact ⟨a,b,ha,hb,fun q hq=>(hboth q hq).1,fun q hq=>(hboth q hq).2,hf.symm⟩

/-- The complete global square criterion in the actual quadratic field:
all prime-multiplicity values are even and both real embeddings positive.
The Euclidean order, fraction representation, and unit-square assertion
are all proved, rather than supplied as assumptions. -/
theorem positive_even_square (x:K) (hx:x≠0)
    (hp:∀(s:ℝ)(hs:s^2=2),0<FiniteScale318.realPlace s hs x)
    (hv:∀(q:O)(hq:Prime q)(m:ℤ),primePlace q hq x=m → Even m) :
    ∃k:K,k^2=x := by
  obtain ⟨a,b,ha,hb,hea,heb,hf⟩:=reduced_even_multiplicity x hx hv
  obtain ⟨r,u,hu⟩:=integral_square_unit a ha hea
  obtain ⟨t,v,hv⟩:=integral_square_unit b hb heb
  let w:Oˣ:=u*v⁻¹
  let z:K:=toK r/toK t
  have ht:t≠0 := by intro hh; rw [hh,zero_pow (by decide),zero_mul] at hv; exact hb hv.symm
  have htk:toK t≠0:=fun hh=>ht (toK_injective (by simpa using hh))
  have hvk:toK (v:O)≠0:=(v.isUnit.map toK).ne_zero
  have hwi:toK (↑(v⁻¹):O)=(toK (v:O))⁻¹ := by
    rw [inv_eq_one_div (toK (v:O))]
    apply (eq_div_iff hvk).mpr
    rw [←map_mul,Units.inv_mul,map_one]
  have hw:toK (w:O)=toK (u:O)/(toK (v:O)) := by
    simp only [w,Units.val_mul,map_mul,hwi,div_eq_mul_inv]
  have he:z^2*toK (w:O)=x := by
    rw [hf,←hu,←hv]
    simp only [map_mul,map_pow]
    rw [hw]
    dsimp only [z]
    field_simp
  have hz:z≠0 := by intro hh; rw [hh,zero_pow (by decide),zero_mul] at he; exact hx he.symm
  have hwp:∀(s:ℝ)(hs:s^2=2),0<FiniteScale318.realPlace s hs (pair (w:O).re (w:O).im) := by
    intro s hs
    let e:=FiniteScale318.realPlace s hs
    have hz':e z≠0:=fun hh=>hz (e.injective (by simpa using hh))
    have hh:=hp s hs
    rw [←he,map_mul,map_pow] at hh
    exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hz')).mp hh
  obtain ⟨k,hk⟩:=PositiveUnitSquare318.totally_positive_unit_square (w:O) w.isUnit hwp
  refine ⟨z*k,?_⟩
  rw [mul_pow,hk]
  exact he

end
end SquareFactorization318
#print axioms SquareFactorization318.integral_square_unit
#print axioms SquareFactorization318.reduced_even_multiplicity
