module
public import ContactProjectiveClosedData318
public import SchemeMonoLocalLift318
public import ContactGlobalZeroClosed318
public section
noncomputable section
namespace ContactProjectiveClosedLocalRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318 ContactProjectiveQuotientGluing318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  {Z : Scheme.{0}} (p : Z ⟶ ContactOriginalRelativePolynomialCharts318.curve R c) [IsClosedImmersion p]
local notation "D" => ContactProjectiveClosedData318.datum R c p
local notation "i" => ContactOriginalRelativePolynomialCharts318.finiteInto R c
local notation "j" => ContactOriginalRelativePolynomialCharts318.infinityInto R c
abbrev finiteComparison : pullback p i ≅ finiteFamily R c D :=
  AffineClosedRestriction318.comparison p (finiteRing R c) i
abbrev infinityComparison : pullback p j ≅ infinityFamily R c D :=
  AffineClosedRestriction318.comparison p (infinityRing R c) j
@[reassoc] lemma finite_comparison_into : (finiteComparison R c p).hom ≫ finiteInto R c D=pullback.snd p i :=
  AffineClosedQuotientExtraction318.comparison_into (finiteRing R c) (pullback.snd p i)
@[reassoc] lemma infinity_comparison_into : (infinityComparison R c p).hom ≫ infinityInto R c D=pullback.snd p j :=
  AffineClosedQuotientExtraction318.comparison_into (infinityRing R c) (pullback.snd p j)
@[expose] def finiteToOriginal : finiteFamily R c D ⟶ Z :=
  (finiteComparison R c p).inv ≫ pullback.fst p i
@[expose] def infinityToOriginal : infinityFamily R c D ⟶ Z :=
  (infinityComparison R c p).inv ≫ pullback.fst p j
@[reassoc] lemma finiteToOriginal_into : finiteToOriginal R c p ≫ p=finiteInto R c D ≫ i := by
  rw [finiteToOriginal,Category.assoc,pullback.condition,← Category.assoc]
  rw [AffineClosedQuotientExtraction318.comparison_inv_into]
@[reassoc] lemma infinityToOriginal_into : infinityToOriginal R c p ≫ p=infinityInto R c D ≫ j := by
  rw [infinityToOriginal,Category.assoc,pullback.condition,← Category.assoc]
  rw [AffineClosedQuotientExtraction318.comparison_inv_into]
end ContactProjectiveClosedLocalRecovery318
