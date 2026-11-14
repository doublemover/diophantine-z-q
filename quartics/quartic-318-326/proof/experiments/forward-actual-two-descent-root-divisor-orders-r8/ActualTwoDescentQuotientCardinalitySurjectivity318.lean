module
public import ActualTwoDescentActualQuotientBound318
public section
noncomputable section
namespace ActualTwoDescentQuotientCardinalitySurjectivity318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentEightClassCube318
open ActualTwoDescentSameRationalBounds318 ActualTwoDescentActualQuotientBound318

/-- If the actual quotient has eight elements, its injection into the actual
candidate cube is surjective. The cardinality is an explicit GLOBAL input. -/
theorem actual_cube_embedding_bijective (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) (hcard : Nat.card (DoubleQuotient (n : ℚ))=8) :
    Function.Bijective (quotientCubeEmbedding n b hn hb H) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨(quotientCubeEmbedding n b hn hb H).injective,hcard.trans cube_card.symm⟩

lemma actual_cube_choice_identity (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) (q : DoubleQuotient (n : ℚ)) :
    ellipticKummerInjection (n : ℚ) (by exact_mod_cast hn) q=
      cubeClass (n : ℚ) (b : ℚ) (by exact_mod_cast hn) (by exact_mod_cast hb)
        (quotientCubeEmbedding n b hn hb H q) :=
  Classical.choose_spec (actual_quotient_cube n b hn hb H q)

/-- Eight actual quotient classes force the literal candidate cube to have
no collisions; no prime-independence premise is substituted for this conclusion. -/
theorem actual_cube_injective_of_eight (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) (hcard : Nat.card (DoubleQuotient (n : ℚ))=8) :
    Function.Injective (cubeClass (n : ℚ) (b : ℚ) (by exact_mod_cast hn) (by exact_mod_cast hb)) := by
  intro u v he
  have hs := (actual_cube_embedding_bijective n b hn hb H hcard).surjective
  obtain ⟨q,hq⟩ := hs u
  obtain ⟨r,hr⟩ := hs v
  have hqr : q=r := by
    apply actual_elliptic_kummer_injective (n : ℚ) (by exact_mod_cast hn)
    rw [actual_cube_choice_identity n b hn hb H q,actual_cube_choice_identity n b hn hb H r,hq,hr]
    exact he
  rw [←hq,←hr,hqr]

/-- Every cube label, in particular beta, is represented by an ACTUAL rational
elliptic point once the actual quotient cardinality eight is supplied. -/
theorem actual_cube_represented_of_eight (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) (hcard : Nat.card (DoubleQuotient (n : ℚ))=8) (v : Cube) :
    ∃ P : Point (n : ℚ), kummerClass (n : ℚ) (by exact_mod_cast hn) P=
      cubeClass (n : ℚ) (b : ℚ) (by exact_mod_cast hn) (by exact_mod_cast hb) v := by
  obtain ⟨q,hq⟩ := (actual_cube_embedding_bijective n b hn hb H hcard).surjective v
  have hrep : ∀ q : DoubleQuotient (n : ℚ), ∃ P : Point (n : ℚ),
      ellipticKummerInjection (n : ℚ) (by exact_mod_cast hn) q=kummerClass (n : ℚ) (by exact_mod_cast hn) P := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro P
    exact ⟨P.toAdd,rfl⟩
  obtain ⟨P,hP⟩ := hrep q
  refine ⟨P,?_⟩
  rw [←hP,actual_cube_choice_identity n b hn hb H q,hq]

end ActualTwoDescentQuotientCardinalitySurjectivity318
