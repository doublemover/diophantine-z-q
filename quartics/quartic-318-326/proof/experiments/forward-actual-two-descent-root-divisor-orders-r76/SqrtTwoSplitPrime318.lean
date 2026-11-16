module
public import SqrtTwoNormDivision318
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
namespace SqrtTwoSplitPrime318

abbrev K := Zsqrtd (2 : ℤ)

private theorem two_nonsquare (n : ℤ) : (2:ℤ) ≠ n*n := by
  intro h
  have hm : (2:ZMod 3)=(n:ZMod 3)*(n:ZMod 3) := by
    simpa using congrArg (fun z : ℤ => (z : ZMod 3)) h
  exact (by decide : ∀ a : ZMod 3, (2:ZMod 3) ≠ a*a) (n:ZMod 3) hm

lemma norm_ne_zero (a : K) (ha : a≠0) : a.norm≠0 :=
  fun hn => ha ((Zsqrtd.norm_eq_zero two_nonsquare a).mp hn)

/-- The previously constructed integer quotient is a literal quotient in
Z[sqrt2], without installing or assuming a EuclideanDomain structure. -/
lemma division (a b : K) (hb : b≠0) :
    ∃ q : K, (a-b*q).norm.natAbs < b.norm.natAbs := by
  have hn : b.re^2-2*b.im^2≠0 := by
    simpa only [Zsqrtd.norm, pow_two, mul_assoc] using norm_ne_zero b hb
  obtain ⟨m,n,h⟩ := SqrtTwoNormDivision318.norm_division a.re a.im b.re b.im hn
  refine ⟨⟨m,n⟩,?_⟩
  have hr : |(a-b*(⟨m,n⟩:K)).norm| < |b.norm| := by
    simpa [Zsqrtd.norm, pow_two, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using h
  rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs]
  exact hr

/-- Minimum-norm descent constructs a generator of any nontrivial kernel.
No principal-ideal or local-global existence assumption is used. -/
theorem kernel_generator {R : Type*} [CommRing R] (f : K →+* R)
    (hex : ∃ x : K, f x=0 ∧ x≠0) :
    ∃ g : K, f g=0 ∧ g≠0 ∧ ∀ x : K, f x=0 → g∣x := by
  classical
  let S : Set K := {x | f x=0 ∧ x≠0}
  obtain ⟨g,hg,hmin⟩ := (measure (fun x : K => x.norm.natAbs)).wf.has_min S hex
  refine ⟨g,hg.1,hg.2,?_⟩
  intro x hx
  obtain ⟨q,hq⟩ := division x g hg.2
  have hr : f (x-g*q)=0 := by simp only [map_sub,map_mul,hx,hg.1,zero_mul,sub_zero]
  have hz : x-g*q=0 := by
    by_contra hn
    exact hmin (x-g*q) ⟨hr,hn⟩ hq
  exact ⟨q,sub_eq_zero.mp hz⟩

/-- A modular square root of2 at a prime gives an actual integral element
of absolute norm p. This is the constructive split-prime component of the
norm criterion, not the auxiliary-prime selection needed for the anchor. -/
theorem prime_norm (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a^2=2) :
    ∃ g : K, g.norm.natAbs=p := by
  classical
  have hp : p.Prime := Fact.out
  let f : K →+* ZMod p := Zsqrtd.lift ⟨a, by simpa [pow_two] using ha⟩
  have hfp : f (p:K)=0 := by simp
  have hp0 : (p:K)≠0 := by
    intro h
    have he := congrArg Zsqrtd.re h
    have : p=0 := by simpa using he
    exact hp.ne_zero this
  obtain ⟨g,hfg,hg0,hg⟩ := kernel_generator f ⟨p,hfp,hp0⟩
  have hgu : ¬IsUnit g := by
    intro hu
    have hf := hu.map f
    rw [hfg] at hf
    exact not_isUnit_zero hf
  obtain ⟨h,hph⟩ := hg (p:K) hfp
  have hprod : p^2=g.norm.natAbs*h.norm.natAbs := by
    have he := congrArg (fun x : K => x.norm.natAbs) hph
    simpa [Zsqrtd.norm_natCast, Zsqrtd.norm_mul, Int.natAbs_mul, pow_two] using he
  obtain ⟨k,hk,hgpow⟩ := (Nat.dvd_prime_pow hp).mp (show g.norm.natAbs∣p^2 from ⟨h.norm.natAbs,hprod⟩)
  interval_cases k
  · exact (hgu (Zsqrtd.norm_eq_one_iff.mp (by simpa using hgpow))).elim
  · exact ⟨g,by simpa using hgpow⟩
  · have hh : h.norm.natAbs=1 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hp.ne_zero)
      simpa only [hgpow, mul_one] using hprod.symm
    obtain ⟨u,hu⟩ := Zsqrtd.norm_eq_one_iff.mp hh
    have hpg : (p:K)∣g := by
      refine ⟨↑(u⁻¹),?_⟩
      rw [hph,←hu]
      simp [mul_assoc]
    let v : K := ⟨-(a.val:ℤ),1⟩
    have hfv : f v=0 := by
      simp [f, v, Zsqrtd.lift]
    have hpv : (p:K)∣v := dvd_trans hpg (hg v hfv)
    have hi : (p:ℤ)∣1 := (Zsqrtd.intCast_dvd (p:ℤ) v).mp hpv |>.2
    have hp1 : p∣1 := by exact_mod_cast hi
    exact (hp.not_dvd_one hp1).elim

end SqrtTwoSplitPrime318
