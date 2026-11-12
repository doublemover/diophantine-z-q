module
public import ContactHilbertIdealCharacterization318
public section
noncomputable section
namespace ContactHilbertFixedRankEquiv318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
/-- Genuine two-sided ALL-point classification of STANDARD full finite,
flat, finitely presented original closed quotients of constant rank n.
The domain has no chart-support, Cartier, local-presentation or parameter
point assumption. Naturality is an additional theorem. -/
@[expose] def equivalence : ContactHilbertData318.FixedRank S c n ≃ ContactProjectiveParameterPoint318.Point c n S :=
  (ContactHilbertIdealCharacterization318.equivalence c n S).trans
    (ContactProjectiveClassifiedEquiv318.equivalence c n S)
lemma full_ideal_recovery (D : ContactHilbertData318.FixedRank S c n) :
    ContactProjectivePointFamily318.idealSheaf c n S (equivalence c n S D)=D.val.ideal :=
  congrArg Subtype.val (ContactProjectiveClassifiedEquiv318.extract_classify c n S
    (ContactHilbertIdealCharacterization318.toClassified c n S D))
end ContactHilbertFixedRankEquiv318
