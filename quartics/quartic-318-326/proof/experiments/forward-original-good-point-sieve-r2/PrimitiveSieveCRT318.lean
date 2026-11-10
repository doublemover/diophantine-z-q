module
public import QuadricCRTAssembly318
public section
noncomputable section
namespace PrimitiveSieveCRT318
open QuadricCRTAssembly318
open scoped BigOperators
set_option maxHeartbeats 1000000

@[expose] def origin {R : Type*} [CommRing R] (κ : R) : Quadric κ :=
  ⟨((0,0),(0,0),0),by simp [equation]⟩

/-- The composite-modulus equation restricts to exactly the previously
counted field quadric; no change of curve or normalization occurs. -/
@[expose] def fieldEquiv {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (κ : F) : Quadric κ ≃ FiniteFiveQuadricCount318.Quadric κ where
  toFun z := ⟨z.1,sub_eq_zero.mp z.2⟩
  invFun z := ⟨z.1,sub_eq_zero.mpr z.2⟩
  left_inv z := rfl
  right_inv z := rfl

@[expose] def nonzeroFieldEquiv {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (κ : F) : {z : Quadric κ // z≠origin κ} ≃
      {z : FiniteFiveQuadricCount318.Quadric κ // z≠FiniteFiveQuadricCount318.origin κ} where
  toFun z := ⟨fieldEquiv κ z.1,by
    intro he
    apply z.2
    apply (fieldEquiv κ).injective
    exact he⟩
  invFun z := ⟨(fieldEquiv κ).symm z.1,by
    intro he
    apply z.2
    apply (fieldEquiv κ).symm.injective
    exact he⟩
  left_inv z := rfl
  right_inv z := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)

/-- Primitive means nonzero at EVERY selected prime. Merely excluding the
one global origin over the composite modulus is strictly weaker. -/
@[expose] def Primitive (κ : ℤ) :=
  Admissible p hp hd κ (fun i => {z | z≠origin (κ : ZMod (p i))})

theorem primitive_card (κ : ℤ) (hp2 : ∀ i, p i≠2) (hκ : ∀ i, ¬(p i:ℤ)∣κ) :
    Nat.card (Primitive p hp hd κ)=∏ i, ((p i)^4-1) := by
  rw [Primitive,admissible_card]
  apply Finset.prod_congr rfl
  intro i hi
  letI : Fact (p i).Prime := ⟨hp i⟩
  rw [Nat.card_congr (nonzeroFieldEquiv (κ : ZMod (p i)))]
  have hF : ringChar (ZMod (p i))≠2 := by simpa only [ringChar_zmod_n] using hp2 i
  have hk : (κ : ZMod (p i))≠0 := by
    intro he
    exact hκ i ((ZMod.intCast_zmod_eq_zero_iff_dvd κ (p i)).mp he)
  simpa only [ZMod.card] using FiniteFiveQuadricCount318.nonzero_quadric_card hF
    (GoodReductionResidue318.two_residue_ne (p i) (hp2 i)) (κ : ZMod (p i)) hk

/-- Exact normalized multiplicativity on the original composite-modulus
quadric. Ω may encode a sieve event, a complement, or extra local constraints;
no analytic independence or asymptotic hypothesis is supplied. -/
theorem normalized_card (κ : ℤ) (hp2 : ∀ i, p i≠2) (hκ : ∀ i, ¬(p i:ℤ)∣κ)
    (Ω : ∀ i, Set (Quadric (κ : ZMod (p i)))) :
    (Nat.card (Admissible p hp hd κ Ω):ℚ)/(Nat.card (Primitive p hp hd κ):ℚ)=
      ∏ i, (Nat.card (Ω i):ℚ)/(((p i)^4-1:ℕ):ℚ) := by
  rw [admissible_card,primitive_card p hp hd κ hp2 hκ]
  simp only [Nat.cast_prod,Finset.prod_div_distrib]

/-- If the specified local sets exclude zero, the constructed global point
really lies in the original primitive source. -/
theorem admissible_primitive (κ : ℤ) (Ω : ∀ i, Set (Quadric (κ : ZMod (p i))))
    (hΩ : ∀ i z, z∈Ω i → z≠origin (κ : ZMod (p i)))
    (z : Admissible p hp hd κ Ω) :
    ∀ i, quadricEquiv p hp hd κ z.1 i≠origin (κ : ZMod (p i)) := by
  intro i
  exact hΩ i _ (z.2 i)

end PrimitiveSieveCRT318
