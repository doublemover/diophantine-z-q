module
public import FractionSqrtTwo318
public import Mathlib.RingTheory.Localization.NumDen
public section
namespace DeltaPrime318
open ConcreteG8Domain EuclideanSqrtTwo318 FractionSqrtTwo318
set_option maxHeartbeats 0
noncomputable section
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

@[expose] def delta:O:=⟨3,-1⟩
@[expose] def residue : O →+* ZMod 7 := Zsqrtd.lift ⟨3,by decide +kernel⟩

theorem residue_apply (u:O) : residue u=(u.re:ZMod 7)+3*u.im := by
  simp [residue,Zsqrtd.lift_apply_apply,mul_comm]

theorem delta_dvd_iff (u:O) : delta∣u ↔ residue u=0 := by
  constructor
  · rintro ⟨v,rfl⟩
    rw [map_mul]
    have hd:residue delta=0 := by rw [residue_apply]; norm_num [delta]
    rw [hd,zero_mul]
  · intro hu
    have hc:((u.re+3*u.im:ℤ):ZMod 7)=0 := by simpa [residue_apply] using hu
    have hd:(7:ℤ)∣u.re+3*u.im := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
    obtain ⟨k,hk⟩:=hd
    refine ⟨⟨3*k-u.im,k⟩,?_⟩
    ext <;> simp [delta,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> omega

theorem delta_prime : Prime delta := by
  refine ⟨?_,?_,?_⟩
  · intro h; have hh:=congrArg Zsqrtd.re h; norm_num [delta] at hh
  · intro h
    have h0:residue delta=0 := (delta_dvd_iff delta).mp dvd_rfl
    exact (h.map residue).ne_zero h0
  · intro a b hab
    have hh:residue a*residue b=0 := by rw [←map_mul]; exact (delta_dvd_iff _).mp hab
    rcases mul_eq_zero.mp hh with ha|hb
    · exact Or.inl ((delta_dvd_iff _).mpr ha)
    · exact Or.inr ((delta_dvd_iff _).mpr hb)

theorem residue_anisotropic : ∀a b:ZMod 7,a^2+4*b^2=0 → a=0 ∧ b=0 := by
  decide +kernel

@[expose] def place : AddValuation K (WithTop ℤ) := primePlace delta delta_prime

theorem value_delta : place (3-i)=1 := by
  have he:toK delta=3-i := by ext <;> norm_num [toK_pair,delta,i,pair,QuadraticAlgebra.re_natCast,QuadraticAlgebra.im_natCast,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
  rw [←he]
  change primePlace delta delta_prime (toK delta)=1
  rw [primePlace_multiplicity delta delta_prime delta delta_prime.ne_zero,
    multiplicity_self (FiniteMultiplicity.of_prime_left delta_prime delta_prime.ne_zero)]
  rfl

theorem integral_value_zero (u:O) (hu:¬delta∣u) : place (toK u)=0 := by
  rw [place,primePlace_integral]
  change enatToInt (emultiplicity delta u)=0
  rw [emultiplicity_eq_zero.mpr hu]
  rfl

theorem value_two : place (2:K)=0 := by
  have he:toK (2:O)=(2:K):=map_ofNat toK 2
  rw [←he]
  apply integral_value_zero
  rw [delta_dvd_iff]
  have hh:residue (2:O)=(2:ZMod 7):=map_ofNat residue 2
  rw [hh]
  decide +kernel

/-- The actual delta residue field prevents a sum a²+4b² from vanishing
whenever b survives reduction. -/
theorem sum_not_dvd (a b:O) (hb:¬delta∣b) : ¬delta∣a^2+4*b^2 := by
  rw [delta_dvd_iff] at hb ⊢
  intro h
  simp only [map_add,map_mul,map_pow,map_ofNat] at h
  exact hb (residue_anisotropic _ _ h).2

/-- The residue obstruction is now lifted to every actual delta-unit in K,
with its reduced numerator/denominator constructed from Euclidean division. -/
theorem square_add_four_value (u:K) (hu:place u=0) : place (u^2+4)=0 := by
  obtain ⟨a,b,ha,hb,hf⟩:=unit_fraction delta delta_prime u hu
  have hb0:toK b≠0 := by
    intro hh
    have he:b=0 := toK_injective (by simpa using hh)
    exact hb (by rw [he]; exact dvd_zero _)
  have he:u^2+4=toK (a^2+4*b^2)/(toK b)^2 := by
    rw [hf]
    simp only [map_add,map_mul,map_pow,map_ofNat]
    field_simp
  rw [he,place.map_div,place.map_pow,integral_value_zero b hb,
    integral_value_zero _ (sum_not_dvd a b hb)]
  simp

theorem dual_even (X Y:K) (m:ℤ) (hX:place X=m) (he:Y^2=X^3+4*D*X) : Even m := by
  have hA:place (4*D)=2 := by
    have hf:(4:K)=2^2 := by norm_num
    rw [place.map_mul,hf,D,place.map_pow,place.map_pow,value_two,value_delta]
    norm_num [two_nsmul]
  rcases DualLocalArithmetic318.dual_delta_even_unless_one place X Y (4*D) m hX hA he with hm|hm
  · exact hm
  subst m
  have hunit:place (X/(3-i))=0 := by rw [place.map_div,hX,value_delta]; norm_num
  have hd:3-i≠(0:K) := (place.ne_top_iff).mp (by rw [value_delta]; simp)
  exact (DualLocalArithmetic318.dual_delta_exception place X Y (3-i) hd value_delta hX
    (square_add_four_value _ hunit) he).elim

end
end DeltaPrime318
#print axioms DeltaPrime318.delta_prime
#print axioms DeltaPrime318.value_delta
#print axioms DeltaPrime318.sum_not_dvd
