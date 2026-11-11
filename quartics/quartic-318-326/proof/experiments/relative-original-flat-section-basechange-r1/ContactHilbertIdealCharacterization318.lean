module
public import ContactPresentedQuotientProperties318
public section
noncomputable section
namespace ContactHilbertIdealCharacterization318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
/-- Every STANDARD finite-flat finitely presented rank-n original
closed quotient has the local chart presentations, derived by N+1
avoidance. Neither a Cartier condition nor a presentation is assumed. -/
@[expose] def toClassified (D : ContactHilbertData318.FixedRank S c n) : ContactProjectiveClassifiedIdeal318.Ideal c n S :=
  ⟨D.val.ideal,⟨ContactHilbertPresentation318.data S c n D⟩⟩
/-- Conversely, the independent local full-ideal condition implies the
standard whole-family finite-flat/FP and true rank conditions. -/
@[expose] def fromClassified (I : ContactProjectiveClassifiedIdeal318.Ideal c n S) : ContactHilbertData318.FixedRank S c n :=
  ⟨{ ideal := I.val
     finite := ContactPresentedQuotientProperties318.finite c n S I.val.subschemeι
       (ContactProjectiveClassifiedIdeal318.presentation c n S I)
     flat := ContactPresentedQuotientProperties318.flat c n S I.val.subschemeι
       (ContactProjectiveClassifiedIdeal318.presentation c n S I)
     presentation := ContactPresentedQuotientProperties318.presentation c n S I.val.subschemeι
       (ContactProjectiveClassifiedIdeal318.presentation c n S I) },
   ContactPresentedQuotientProperties318.rank c n S I.val.subschemeι
     (ContactProjectiveClassifiedIdeal318.presentation c n S I)⟩
@[expose] def equivalence : ContactHilbertData318.FixedRank S c n ≃ ContactProjectiveClassifiedIdeal318.Ideal c n S where
  toFun := toClassified c n S
  invFun := fromClassified c n S
  left_inv D := by apply Subtype.ext; apply ContactHilbertData318.Datum.ext; rfl
  right_inv I := by apply Subtype.ext; rfl
end ContactHilbertIdealCharacterization318
