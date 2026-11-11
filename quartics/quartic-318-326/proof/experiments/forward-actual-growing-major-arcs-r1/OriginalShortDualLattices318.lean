module
public import OriginalBoundedDualSum318
public section
noncomputable section
namespace OriginalShortDualLattices318
open scoped BigOperators
open TernaryQuadraticLineCover318 NonzeroMultipleBox318 TriangularLatticeBoxCount318
open OriginalDualIncidenceCount318 LiteralTernaryReduction318 LiteralIntegerDuality318
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual original lattice parameters with a NONZERO integer annihilator
in the original coordinate box. The modulus is the original squarefree
modulus. This is not yet a statement about a Euclidean minimum. -/
@[expose] def ShortDual (p : ι → ℕ) (κ : ℤ) (B : ℕ) :=
  {t : ∀ i, Option (ZMod (p i)) // ∃ v : NonzeroBox B,
    ∀ u : Vector ℤ, u∈literalLattice p κ t →
      (FixedSquarefreeCRT318.modulus p:ℤ)∣dot (coordinates v.1) u}

/-- Selecting an actual witness injects the UNION into the incidence
space. It never counts lattice parameters as if witnesses were unique. -/
@[expose] def chooseIncidence (p : ι → ℕ) (κ : ℤ) (B : ℕ) :
    ShortDual p κ B → Σ v : NonzeroBox B, Incidence p κ (coordinates v.1) := fun t =>
  ⟨Classical.choose t.2,⟨t.1,Classical.choose_spec t.2⟩⟩

lemma chooseIncidence_injective (p : ι → ℕ) (κ : ℤ) (B : ℕ) :
    Function.Injective (chooseIncidence p κ B) := by
  intro s t he
  apply Subtype.ext
  exact congrArg (fun z : Σ v : NonzeroBox B, Incidence p κ (coordinates v.1) => z.2.1) he

/-- Quantitative bound for the actual short-integer-dual exceptional
lattice family, with zero excluded and every bad local reduction counted.
A separate geometric theorem must connect a large third minimum to this
explicit family before a successive-minima tail can be claimed. -/
theorem original_short_dual_bound (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ) (B : ℕ) :
    Nat.card (ShortDual p κ B)≤27*4^(Fintype.card ι)*B^3 := by
  classical
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  have hh := Nat.card_le_card_of_injective (chooseIncidence p κ B)
    (chooseIncidence_injective p κ B)
  calc
    _ ≤ Nat.card (Σ v : NonzeroBox B, Incidence p κ (coordinates v.1)) := hh
    _ = ∑ v : NonzeroBox B, Nat.card (Incidence p κ (coordinates v.1)) := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ ≤ 27*4^(Fintype.card ι)*B^3 :=
      OriginalBoundedDualSum318.original_bounded_dual_sum p hp hd κ hκ B

end OriginalShortDualLattices318
