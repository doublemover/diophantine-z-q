module
public import ContactProjectiveClosedRecovery318
public section
noncomputable section
namespace ContactProjectiveDatumRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318 ContactProjectiveQuotientGluing318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
lemma finite_ideal : ContactProjectiveClosedData318.finiteIdeal R c (into R c D)=D.finiteIdeal := by
  let h := finite_square R c D
  apply AffineClosedQuotientExtraction318.ideal_unique (finiteRing R c)
    (pullback.snd (into R c D) (ContactOriginalRelativePolynomialCharts318.finiteInto R c))
    D.finiteIdeal h.isoPullback.symm
  exact h.isoPullback_inv_snd
lemma infinity_ideal : ContactProjectiveClosedData318.infinityIdeal R c (into R c D)=D.infinityIdeal := by
  let h := infinity_square R c D
  apply AffineClosedQuotientExtraction318.ideal_unique (infinityRing R c)
    (pullback.snd (into R c D) (ContactOriginalRelativePolynomialCharts318.infinityInto R c))
    D.infinityIdeal h.isoPullback.symm
  exact h.isoPullback_inv_snd
/-- Entire compatible ideal data, not just quotient isomorphism classes,
are recovered after gluing to the original source. -/
lemma datum : ContactProjectiveClosedData318.datum R c (into R c D)=D := by
  have hf := finite_ideal R c D
  have hi := infinity_ideal R c D
  cases D
  simp_all [ContactProjectiveClosedData318.datum]
end ContactProjectiveDatumRecovery318
