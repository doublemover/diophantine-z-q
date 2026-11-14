module
public import TernaryChartModuli318
public section
noncomputable section
namespace OriginalTernaryBasis318
open TernaryQuadraticLineCover318 TernaryCongruenceLattices318 TernaryChartModuli318
open TriangularTernaryBasis318
set_option maxHeartbeats 1000000

lemma infinity_code (p : ℕ) [Fact p.Prime] (κ : ℤ) (v : Vector ℤ) :
    integerCode p κ none v=0 ↔ (p:ℤ)∣v.1 ∧ (p:ℤ)∣v.2.2 := by
  change ((v.1:ZMod p),(v.2.2:ZMod p))=(0,0) ↔ _
  simp only [Prod.mk.injEq,ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma finite_code (p : ℕ) [Fact p.Prime] (κ A B : ℤ) (s : ZMod p)
    (hA : (A:ZMod p)=(κ:ZMod p)*s^2*(2:ZMod p)⁻¹) (hB : (B:ZMod p)=s)
    (v : Vector ℤ) : integerCode p κ (some s) v=0 ↔
      (p:ℤ)∣v.2.1-A*v.1 ∧ (p:ℤ)∣v.2.2-B*v.1 := by
  have he : integerCode p κ (some s) v=
      (((v.2.1-A*v.1:ℤ):ZMod p),((v.2.2-B*v.1:ℤ):ZMod p)) := by
    apply Prod.ext
    · change (v.2.1:ZMod p)-(κ:ZMod p)*s^2*(v.1:ZMod p)/2=
        ((v.2.1-A*v.1:ℤ):ZMod p)
      push_cast
      rw [hA]
      rw [div_eq_mul_inv]
      ring
    · change (v.2.2:ZMod p)-s*(v.1:ZMod p)=((v.2.2-B*v.1:ℤ):ZMod p)
      push_cast
      rw [hB]
  rw [he]
  change (_,_ )=(0,0) ↔ _
  simp only [Prod.mk.injEq,ZMod.intCast_zmod_eq_zero_iff_dvd]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original globally coded lattice equals the actual mixed-chart
triangular congruences for coefficients produced on its finite directions. -/
theorem membership_iff (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (κ A B : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (hcoeff : ∀ i, t i≠none →
      (A : ZMod (p i))=(κ : ZMod (p i))*((t i).getD 0)^2*(2 : ZMod (p i))⁻¹ ∧
      (B : ZMod (p i))=(t i).getD 0) (v : Vector ℤ) :
    v∈SquarefreeTernaryLatticeCover318.lattice p hp κ t ↔
      Conditions (finiteModulus p t:ℤ) (infinityModulus p t:ℤ) A B v := by
  classical
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  let pf (i : FiniteIndex t) := p i.1
  let pr (i : InfinityIndex t) := p i.1
  have hpf (i : FiniteIndex t) : (pf i).Prime := hp i.1
  have hpr (i : InfinityIndex t) : (pr i).Prime := hp i.1
  have hdf : Function.Injective pf := hd.comp Subtype.val_injective
  have hdr : Function.Injective pr := hd.comp Subtype.val_injective
  have hfdiv (n : ℤ) : (finiteModulus p t:ℤ)∣n ↔ ∀ i : FiniteIndex t, (p i.1:ℤ)∣n :=
    SquarefreeTernaryLatticeCover318.product_divisor_iff pf hpf hdf n
  have hrdiv (n : ℤ) : (infinityModulus p t:ℤ)∣n ↔ ∀ i : InfinityIndex t, (p i.1:ℤ)∣n :=
    SquarefreeTernaryLatticeCover318.product_divisor_iff pr hpr hdr n
  have hqr : (finiteModulus p t:ℤ)*(infinityModulus p t:ℤ)=
      (FixedSquarefreeCRT318.modulus p:ℤ) := by exact_mod_cast moduli_product p t
  have hboth (n : ℤ) : (finiteModulus p t:ℤ)*(infinityModulus p t:ℤ)∣n ↔
      ∀ i, (p i:ℤ)∣n := by
    rw [hqr]
    exact SquarefreeTernaryLatticeCover318.product_divisor_iff p hp hd n
  have hlocal : v∈SquarefreeTernaryLatticeCover318.lattice p hp κ t ↔
      ∀ i, integerCode (p i) κ (t i) v=0 := by
    change SquarefreeTernaryLatticeCover318.globalCode p hp κ t v=0 ↔ _
    exact ⟨fun h i => congrFun h i,fun h => funext h⟩
  rw [hlocal,Conditions,hrdiv,hfdiv,hboth]
  constructor
  · intro hv
    refine ⟨?_,?_,?_⟩
    · intro i
      have ht : t i.1=none := Classical.not_not.mp i.2
      have hh := hv i.1
      rw [ht] at hh
      exact ((infinity_code (p i.1) κ v).mp hh).1
    · intro i
      have hc := hcoeff i.1 i.2
      cases ht : t i.1 with
      | none => exact False.elim (i.2 ht)
      | some s =>
        rw [ht] at hc
        have hh := hv i.1
        rw [ht] at hh
        exact ((finite_code (p i.1) κ A B s hc.1 hc.2 v).mp hh).1
    · intro i
      cases ht : t i with
      | none =>
        have hh := hv i
        rw [ht] at hh
        obtain ⟨hx,hw⟩ := (infinity_code (p i) κ v).mp hh
        exact dvd_sub hw (dvd_mul_of_dvd_right hx B)
      | some s =>
        have hc := hcoeff i (by rw [ht]; simp)
        rw [ht] at hc
        have hh := hv i
        rw [ht] at hh
        exact ((finite_code (p i) κ A B s hc.1 hc.2 v).mp hh).2
  · rintro ⟨hx,hz,hw⟩ i
    cases ht : t i with
    | none =>
      rw [ht]
      apply (infinity_code (p i) κ v).mpr
      have hxi := hx ⟨i,by simp [ht]⟩
      refine ⟨hxi,?_⟩
      have hh := dvd_add (hw i) (dvd_mul_of_dvd_right hxi B)
      simpa only [sub_add_cancel] using hh
    | some s =>
      have hi : t i≠none := by rw [ht]; simp
      have hc := hcoeff i hi
      rw [ht] at hc ⊢
      exact (finite_code (p i) κ A B s hc.1 hc.2 v).mpr ⟨hz ⟨i,hi⟩,hw i⟩

/-- Produce an actual integral basis for EVERY original congruence lattice,
with unique integral coordinates and generators in the box [-q,q]^3 for
the original squarefree q. No basis, reduction map or bounded representatives
are caller inputs. -/
theorem original_bounded_basis (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ q r A B : ℤ, 0<q ∧ 0<r ∧ q*r=(FixedSquarefreeCRT318.modulus p:ℤ) ∧
      0≤A ∧ A<q ∧ 0≤B ∧ B<q ∧
      (∀ v : Vector ℤ, v∈SquarefreeTernaryLatticeCover318.lattice p hp κ t ↔
        ∃! u : Vector ℤ, basisMap q r A B u=v) ∧
      Within (FixedSquarefreeCRT318.modulus p:ℤ) (first r A B) ∧
      Within (FixedSquarefreeCRT318.modulus p:ℤ) (second q) ∧
      Within (FixedSquarefreeCRT318.modulus p:ℤ) (third q r) := by
  obtain ⟨A,B,hA0,hA,hB0,hB,hcoeff⟩ := original_coefficients p hp hd κ t
  obtain ⟨hq,hr⟩ := moduli_positive p hp t
  have hqz : (0:ℤ)<finiteModulus p t := by exact_mod_cast hq
  have hrz : (0:ℤ)< infinityModulus p t := by exact_mod_cast hr
  have hqr : (finiteModulus p t:ℤ)*(infinityModulus p t:ℤ)=
      (FixedSquarefreeCRT318.modulus p:ℤ) := by exact_mod_cast moduli_product p t
  refine ⟨(finiteModulus p t:ℤ),(infinityModulus p t:ℤ),A,B,hqz,hrz,hqr,hA0,hA,hB0,hB,?_,?_⟩
  · intro v
    rw [membership_iff p hp hd κ A B t hcoeff v]
    constructor
    · exact unique_coordinates _ _ A B (ne_of_gt hqz) (ne_of_gt hrz) v
    · intro hv
      exact (conditions_iff_image _ _ A B v).mpr hv.exists
  · have hb := basis_box_bound _ _ A B hqz hrz hA0 hA hB0 hB
    rwa [hqr] at hb

end OriginalTernaryBasis318
