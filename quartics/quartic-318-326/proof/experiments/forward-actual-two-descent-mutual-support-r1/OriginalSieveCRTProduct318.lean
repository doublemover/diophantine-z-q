module
public import PrimitiveSieveCRT318
public section
noncomputable section
namespace OriginalSieveCRTProduct318
open QuadricCRTAssembly318 PrimitiveSieveCRT318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Literal original coefficient-divisibility event, excluding only the
zero vector in each local field. The coefficient indices are unchanged. -/
@[expose] def badSet {R : Type*} [CommRing R] (κ : R) (γ : J → R) : Set (Quadric κ) :=
  {z | z≠PrimitiveSieveCRT318.origin κ ∧
    ∃ j, z.1.1.1^2+z.1.1.2^2+γ j*z.1.2.2^2=0}

@[expose] def badEquiv {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (κ : F) (γ : J → F) (j₀ : J) : badSet κ γ ≃
      {z : FiniteSieveDensity318.Total κ γ // z≠FiniteSieveDensity318.totalOrigin κ γ j₀} where
  toFun z := ⟨⟨fieldEquiv κ z.1,z.2.2⟩,by
    intro he
    apply z.2.1
    apply (fieldEquiv κ).injective
    exact congrArg Subtype.val he⟩
  invFun z := ⟨(fieldEquiv κ).symm z.1.1,by
    constructor
    · intro he
      apply z.2
      apply Subtype.ext
      apply (fieldEquiv κ).symm.injective
      exact he
    · exact z.1.2⟩
  left_inv z := rfl
  right_inv z := rfl

/-- The local count in the CRT numerator is exactly the earlier literal
sieve density, including all exceptional w=0 fibers. -/
theorem local_density (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (κ : ℤ)
    (hκ : ¬(p:ℤ)∣κ) (γ : J → ℤ) (j₀ : J) :
    (Nat.card (badSet (κ : ZMod p) (fun j => (γ j : ZMod p))):ℚ)/((p^4-1:ℕ):ℚ)=
      FiniteSieveDensity318.density (κ : ZMod p) (fun j => (γ j : ZMod p)) j₀ := by
  rw [FiniteSieveDensity318.density,←Nat.card_congr (badEquiv (κ : ZMod p)
    (fun j => (γ j : ZMod p)) j₀)]
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hk : (κ : ZMod p)≠0 := by
    intro he
    exact hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp he)
  rw [FiniteFiveQuadricCount318.nonzero_quadric_card hF
    (GoodReductionResidue318.two_residue_ne p hp2) (κ : ZMod p) hk,ZMod.card]

@[expose] def densityAt (p : ℕ) (hp : p.Prime) (κ : ℤ) (γ : J → ℤ) (j₀ : J) : ℚ :=
  letI : Fact p.Prime := ⟨hp⟩
  FiniteSieveDensity318.density (κ : ZMod p) (fun j => (γ j : ZMod p)) j₀

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)

/-- Simultaneous original sieve divisibility at the selected primes on
ONE original quadric modulo their product. -/
@[expose] def SimultaneousBad (κ : ℤ) (γ : J → ℤ) :=
  Admissible p hp hd κ (fun i => badSet (κ : ZMod (p i)) (fun j => (γ j : ZMod (p i))))

/-- The original local density factors really multiply for this original
congruence event. This is exact finite CRT, not an asymptotic for integer
points or a claim about simultaneous Gaussian primality. -/
theorem simultaneous_density (κ : ℤ) (hp2 : ∀ i, p i≠2) (hκ : ∀ i, ¬(p i:ℤ)∣κ)
    (γ : J → ℤ) (j₀ : J) :
    (Nat.card (SimultaneousBad p hp hd κ γ):ℚ)/(Nat.card (Primitive p hp hd κ):ℚ)=
      ∏ i, densityAt (p i) (hp i) κ γ j₀ := by
  rw [SimultaneousBad,normalized_card p hp hd κ hp2 hκ]
  apply Finset.prod_congr rfl
  intro i hi
  letI : Fact (p i).Prime := ⟨hp i⟩
  exact local_density (p i) (hp2 i) κ (hκ i) γ j₀

/-- Every actual simultaneous sieve point is primitive at EACH prime. -/
theorem simultaneous_primitive (κ : ℤ) (γ : J → ℤ)
    (z : SimultaneousBad p hp hd κ γ) :
    ∀ i, quadricEquiv p hp hd κ z.1 i≠PrimitiveSieveCRT318.origin (κ : ZMod (p i)) := by
  intro i
  exact (z.2 i).1

end OriginalSieveCRTProduct318
