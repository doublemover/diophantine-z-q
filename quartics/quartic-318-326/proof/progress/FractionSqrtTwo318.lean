module
public import EuclideanSqrtTwo318
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Valuation.PrimeMultiplicity
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public section
namespace FractionSqrtTwo318
open ConcreteG8Domain EuclideanSqrtTwo318
set_option maxHeartbeats 0
noncomputable section

instance : Algebra O K := toK.toAlgebra
instance : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).mpr toK_injective

theorem exists_fraction (x:K) : ∃a b:O,x=toK a/toK b := by
  obtain ⟨a,b⟩:=x
  let n:O:=⟨a.num*b.den,b.num*a.den⟩
  let d:O:=⟨(a.den:ℤ)*b.den,0⟩
  have hd:toK d≠0 := by
    intro hh
    have he:=congrArg QuadraticAlgebra.re hh
    simp only [toK_pair,d,pair] at he
    norm_num at he
  refine ⟨n,d,(eq_div_iff hd).mpr ?_⟩
  change pair a b*toK d=toK n
  simp only [toK_pair,d,n]
  push_cast
  rw [pair_product]
  ext <;> simp only [pair,mul_zero,mul_one,add_zero,zero_add]
  · rw [←mul_assoc,Rat.mul_den_eq_num]
  · rw [mul_comm (a.den:ℚ),←mul_assoc,Rat.mul_den_eq_num]

instance : IsFractionRing O K := IsFractionRing.of_field O K exists_fraction

@[expose] def enatToInt : ℕ∞ →+o WithTop ℤ where
  toFun n:=n.map (fun m:ℕ=>(m:ℤ))
  map_zero':=rfl
  map_add' a b:=by
    cases a with
    | top => cases b with
      | top => change (⊤:WithTop ℤ)=⊤+⊤; simp
      | coe b => change (⊤:WithTop ℤ)=⊤+(b:ℤ); simp
    | coe a => cases b with
      | top => change (⊤:WithTop ℤ)=(a:ℤ)+⊤; simp
      | coe b => change (((a+b:ℕ):ℤ):WithTop ℤ)=(a:ℤ)+(b:ℤ); norm_cast
  monotone' := by
    intro a b hab
    cases a with
    | top => cases b with
      | top => exact le_refl _
      | coe b => exact (not_le_of_gt (ENat.coe_lt_top b) hab).elim
    | coe a => cases b with
      | top => exact le_top
      | coe b =>
        change ((a:ℤ):WithTop ℤ)≤(b:ℤ)
        have hh:a≤b := by exact_mod_cast hab
        exact_mod_cast hh


@[expose] def integralPlace (q:O) (hq:Prime q) : AddValuation O (WithTop ℤ) :=
  (multiplicity_addValuation hq).map enatToInt rfl

theorem integralPlace_finite (q:O) (hq:Prime q) (u:O) (hu:u≠0) :
    integralPlace q hq u=(multiplicity q u:ℤ) := by
  change enatToInt (emultiplicity q u)=_
  rw [(FiniteMultiplicity.of_prime_left hq hu).emultiplicity_eq_multiplicity]
  rfl

theorem integralPlace_support (q:O) (hq:Prime q) :
    nonZeroDivisors O ≤ (AddValuation.toValuation (integralPlace q hq)).supp.primeCompl := by
  intro u hu
  have hu0:u≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hu
  change integralPlace q hq u≠⊤
  rw [integralPlace_finite q hq u hu0]
  simp

@[expose] def primePlace (q:O) (hq:Prime q) : AddValuation K (WithTop ℤ) :=
  AddValuation.ofValuation ((AddValuation.toValuation (integralPlace q hq)).extendToLocalization
    (integralPlace_support q hq) K)

theorem primePlace_integral (q:O) (hq:Prime q) (u:O) :
    primePlace q hq (toK u)=integralPlace q hq u := by
  change (AddValuation.toValuation (integralPlace q hq)).extendToLocalization
    (integralPlace_support q hq) K (algebraMap O K u)=_
  rw [Valuation.extendToLocalization_apply_map_apply]
  rfl

theorem primePlace_multiplicity (q:O) (hq:Prime q) (u:O) (hu:u≠0) :
    primePlace q hq (toK u)=(multiplicity q u:ℤ) := by
  rw [primePlace_integral,integralPlace_finite q hq u hu]

theorem primePlace_not_dvd (q:O) (hq:Prime q) (u:O) (hu:¬q∣u) :
    primePlace q hq (toK u)=0 := by
  rw [primePlace_integral]
  change enatToInt (emultiplicity q u)=0
  rw [emultiplicity_eq_zero.mpr hu]
  rfl

theorem primePlace_associated (q r:O) (hq:Prime q) (hr:Prime r) (h:Associated q r) :
    primePlace q hq=primePlace r hr := by
  apply AddValuation.ext
  intro x
  obtain ⟨a,b,rfl⟩:=exists_fraction x
  rw [(primePlace q hq).map_div,(primePlace r hr).map_div]
  congr 1 <;> rw [primePlace_integral,primePlace_integral]
  all_goals change enatToInt (emultiplicity q _)=enatToInt (emultiplicity r _)
  all_goals rw [emultiplicity_eq_of_associated_left h]

/-- An actual value-zero fraction admits numerator and denominator both
prime-to-q, using the proved Euclidean structure rather than a local input. -/
theorem unit_fraction (q:O) (hq:Prime q) (x:K) (hx:primePlace q hq x=0) :
    ∃a b:O,¬q∣a ∧ ¬q∣b ∧ x=toK a/toK b := by
  obtain ⟨a,b,hab,hf⟩:=IsFractionRing.exists_reduced_fraction O x
  rw [IsFractionRing.mk'_eq_div] at hf
  change toK a/toK b=x at hf
  have hb:(b:O)≠0:=mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have ha:a≠0 := by
    intro hh
    rw [hh,map_zero,zero_div] at hf
    rw [←hf,(primePlace q hq).map_zero] at hx
    exact WithTop.top_ne_coe hx
  have hv:=hx
  rw [←hf,(primePlace q hq).map_div,primePlace_multiplicity q hq a ha,
    primePlace_multiplicity q hq b hb] at hv
  have he: multiplicity q a=multiplicity q b := by
    have ht:(multiplicity q a:ℤ)-(multiplicity q b:ℤ)=0 := by exact_mod_cast hv
    omega
  have hna:¬q∣a := by
    intro hd
    have hnb:q∣(b:O) := by
      by_contra hh
      have hz:=multiplicity_eq_zero_of_not_dvd hh
      rw [←he] at hz
      exact ((multiplicity_eq_zero (FiniteMultiplicity.of_prime_left hq ha)).mp hz) hd
    exact hq.not_isUnit (hab hd hnb)
  have hnb:¬q∣(b:O) := by
    have hz:=multiplicity_eq_zero_of_not_dvd hna
    rw [he] at hz
    exact (multiplicity_eq_zero (FiniteMultiplicity.of_prime_left hq hb)).mp hz
  exact ⟨a,b,hna,hnb,hf.symm⟩

end
end FractionSqrtTwo318
#print axioms FractionSqrtTwo318.primePlace
#print axioms FractionSqrtTwo318.primePlace_multiplicity
