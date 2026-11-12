module
public import FixedSieveExceptionalPrimes318
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Fintype.EquivFin
public section
noncomputable section
namespace FixedSquarefreeCRT318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def modulus (p : ι → ℕ) : ℕ := ∏ i : ι, p i
lemma modulus_positive (p : ι → ℕ) (hp : ∀ i, (p i).Prime) : 0<modulus p := by
  apply Finset.prod_pos
  intro i hi
  exact (hp i).pos

@[expose] def component (p : ι → ℕ) (i : ι) : ZMod (modulus p) →+* ZMod (p i) :=
  ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i))

@[expose] def reduce (p : ι → ℕ) : ZMod (modulus p) →+* (∀ i : ι, ZMod (p i)) :=
  RingHom.pi (component p)

/-- The simultaneous residue map is onto by the actual finite-index CRT,
not an assumed independent-choice property of local conditions. -/
theorem reduce_surjective (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) : Function.Surjective (reduce p) := by
  classical
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  intro z
  have hn : ∀ i∈(Finset.univ:Finset ι), p i≠0 := fun i _ => (hp i).ne_zero
  have hpair : Set.Pairwise (Finset.univ:Finset ι) (Nat.Coprime on p) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun he => hij (hd he))
  let n := Nat.chineseRemainderOfFinset (fun i => (z i).val) p Finset.univ hn hpair
  refine ⟨(n.val:ZMod (modulus p)),?_⟩
  funext i
  change component p i (n.val:ZMod (modulus p))=z i
  rw [map_natCast]
  have he := (ZMod.natCast_eq_natCast_iff n.val (z i).val (p i)).mpr (n.2 i (Finset.mem_univ i))
  exact he.trans (ZMod.natCast_zmod_val (z i))

/-- Actual finite cardinalities turn the surjective CRT map into an
isomorphism; the empty prime index set is included (modulus1). -/
theorem reduce_bijective (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) : Function.Bijective (reduce p) := by
  classical
  letI : NeZero (modulus p) := ⟨Nat.ne_of_gt (modulus_positive p hp)⟩
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  have hc : Fintype.card (ZMod (modulus p))=Fintype.card (∀ i : ι, ZMod (p i)) := by
    simp only [ZMod.card,Fintype.card_pi,modulus]
  let e : ZMod (modulus p) ≃ (∀ i : ι, ZMod (p i)) := Fintype.equivOfCardEq hc
  have hs := reduce_surjective p hp hd
  have hcomp : Function.Surjective (e.symm ∘ reduce p) := e.symm.surjective.comp hs
  have hinj := (Finite.injective_iff_surjective).mpr hcomp
  refine ⟨?_,hs⟩
  intro x y he
  apply hinj
  exact congrArg e.symm he

@[expose] def ringEquiv (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) : ZMod (modulus p) ≃+* (∀ i : ι, ZMod (p i)) :=
  RingEquiv.ofBijective (reduce p) (reduce_bijective p hp hd)

lemma ringEquiv_component (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (x : ZMod (modulus p)) (i : ι) :
    ringEquiv p hp hd x i=component p i x := rfl

end FixedSquarefreeCRT318
