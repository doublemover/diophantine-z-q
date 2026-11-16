module
public import TernaryCongruenceLattices318
public section
noncomputable section
namespace SquarefreeTernaryLatticeCover318
open TernaryQuadraticLineCover318 TernaryCongruenceLattices318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)

include hp hd in
/-- Actual simultaneous integer representatives, using the already
constructed residue ring CRT rather than a new lifting hypothesis. -/
lemma integer_residue_lift (f : ∀ i, ZMod (p i)) :
    ∃ a : ℤ, ∀ i, (a : ZMod (p i))=f i := by
  letI : NeZero (FixedSquarefreeCRT318.modulus p) :=
    ⟨Nat.ne_of_gt (FixedSquarefreeCRT318.modulus_positive p hp)⟩
  let y := (FixedSquarefreeCRT318.ringEquiv p hp hd).symm f
  refine ⟨(y.val:ℤ),?_⟩
  intro i
  rw [Int.cast_natCast,←map_natCast (FixedSquarefreeCRT318.component p i) y.val,
    ZMod.natCast_zmod_val]
  exact congrFun ((FixedSquarefreeCRT318.ringEquiv p hp hd).apply_symm_apply f) i

@[expose] def globalCode (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    Vector ℤ →+ (∀ i, ZMod (p i)×ZMod (p i)) :=
  AddMonoidHom.pi (fun i => @integerCode (p i) ⟨hp i⟩ κ (t i))

include hd in
lemma global_code_surjective (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    Function.Surjective (globalCode p hp κ t) := by
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  intro y
  let z (i : ι) : Vector (ZMod (p i)) := sectionVector (t i) (y i)
  obtain ⟨a,ha⟩ := integer_residue_lift p hp hd (fun i => (z i).1)
  obtain ⟨b,hb⟩ := integer_residue_lift p hp hd (fun i => (z i).2.1)
  obtain ⟨c,hc⟩ := integer_residue_lift p hp hd (fun i => (z i).2.2)
  refine ⟨(a,b,c),?_⟩
  funext i
  change lineCode (κ : ZMod (p i)) (t i) (reduce (p i) (a,b,c))=y i
  have hred : reduce (p i) (a,b,c)=z i := by
    change ((a:ZMod (p i)),(b:ZMod (p i)),(c:ZMod (p i)))=z i
    rw [ha i,hb i,hc i]
  rw [hred]
  exact code_section (κ : ZMod (p i)) (t i) (y i)

@[expose] def lattice (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) : AddSubgroup (Vector ℤ) :=
  (globalCode p hp κ t).ker

include hd in
/-- Exact full index q² of every actual integer congruence lattice. -/
theorem lattice_index (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    (lattice p hp κ t).index=(FixedSquarefreeCRT318.modulus p)^2 := by
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  rw [lattice,AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (globalCode p hp κ t)
      (global_code_surjective p hp hd κ t)).toEquiv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_pi,Fintype.card_prod,ZMod.card,
    FixedSquarefreeCRT318.modulus,pow_two,Finset.prod_mul_distrib]

include hp hd in
lemma product_divisor_iff (n : ℤ) :
    (FixedSquarefreeCRT318.modulus p:ℤ)∣n ↔ ∀ i, (p i:ℤ)∣n := by
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hn i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd n (p i)).mp
    have hh := congrArg (FixedSquarefreeCRT318.component p i) hn
    simpa only [map_intCast,map_zero] using hh
  · intro hn
    apply (FixedSquarefreeCRT318.ringEquiv p hp hd).injective
    funext i
    change FixedSquarefreeCRT318.component p i (n : ZMod (FixedSquarefreeCRT318.modulus p))=0
    rw [map_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd n (p i)).mpr (hn i)

include hd in
/-- Actual squarefree ternary divisibility is covered by the constructed
integer lattices, with all original coordinates and coefficients retained. -/
theorem divisor_iff_lattice (κ : ℤ) (hp2 : ∀ i, p i≠2) (hκ : ∀ i, ¬(p i:ℤ)∣κ)
    (v : Vector ℤ) :
    (FixedSquarefreeCRT318.modulus p:ℤ)∣κ*v.2.2^2-2*v.1*v.2.1 ↔
      ∃ t : ∀ i, Option (ZMod (p i)), v∈lattice p hp κ t := by
  classical
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  rw [product_divisor_iff p hp hd]
  constructor
  · intro hv
    have hh (i : ι) := (TernaryCongruenceLattices318.divisor_iff_lattice (p i) (hp2 i) κ (hκ i) v).mp (hv i)
    choose t ht using hh
    refine ⟨t,?_⟩
    change globalCode p hp κ t v=0
    funext i
    exact ht i
  · rintro ⟨t,ht⟩ i
    apply (TernaryCongruenceLattices318.divisor_iff_lattice (p i) (hp2 i) κ (hκ i) v).mpr
    refine ⟨t i,?_⟩
    change globalCode p hp κ t v=0 at ht
    exact congrFun ht i

include hp in
/-- At most 2^omega(q)*q indexed lattices, stronger than the coarse
9^omega(q)*q count needed in the manuscript. No Euclidean basis/minima
estimate is inferred from this finite-index statement. -/
theorem parameter_bound :
    Nat.card (∀ i, Option (ZMod (p i)))≤
      2^(Fintype.card ι)*FixedSquarefreeCRT318.modulus p := by
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  simp only [Nat.card_eq_fintype_card,Fintype.card_pi,Fintype.card_option,ZMod.card]
  calc
    ∏ i, (p i+1)≤∏ i, (2*p i) := by
      apply Finset.prod_le_prod'
      intro i hi
      have hh := (hp i).two_le
      omega
    _ = 2^(Fintype.card ι)*FixedSquarefreeCRT318.modulus p := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ,FixedSquarefreeCRT318.modulus]

end SquarefreeTernaryLatticeCover318
