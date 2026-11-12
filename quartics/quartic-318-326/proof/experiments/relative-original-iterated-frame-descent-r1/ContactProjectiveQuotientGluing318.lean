module
public import ContactProjectiveQuotientOverlap318
public import SchemeTwoOpenClosedDescent318
public section
noncomputable section
namespace ContactProjectiveQuotientGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318 ContactProjectiveQuotientOverlap318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
local notation "f" => ContactOriginalRelativeOverlap318.finiteEdge R c
local notation "g" => ContactOriginalRelativeOverlap318.infinityEdge R c
local notation "i" => ContactOriginalRelativePolynomialCharts318.finiteInto R c
local notation "j" => ContactOriginalRelativePolynomialCharts318.infinityInto R c
local notation "hb" => ContactOriginalChartIntersection318.cartesian R c
local notation "a" => finiteMap R c D
local notation "b" => infinityMap R c D
local notation "p" => finiteInto R c D
local notation "q" => infinityInto R c D
local notation "r" => overlapInto R c D
local notation "ha" => finite_cartesian R c D
local notation "hc" => infinity_cartesian R c D
abbrev family : Scheme := pushout a b
abbrev finiteChart : finiteFamily R c D ⟶ family R c D := pushout.inl a b
abbrev infinityChart : infinityFamily R c D ⟶ family R c D := pushout.inr a b
/-- Actual glued quotient on the unchanged original projective family. -/
@[expose] def into : family R c D ⟶ ContactOriginalRelativePolynomialCharts318.curve R c :=
  SchemeClosedOpenPushout318.map f g i j hb a b p q r ha hc
lemma finite_square : IsPullback (finiteChart R c D) p (into R c D) i :=
  SchemeClosedOpenPushout318.left_cartesian f g i j hb a b p q r ha hc
lemma infinity_square : IsPullback (infinityChart R c D) q (into R c D) j :=
  SchemeClosedOpenPushout318.right_cartesian f g i j hb a b p q r ha hc
instance closed : IsClosedImmersion (into R c D) :=
  SchemeTwoOpenClosedDescent318.closed i j (ContactOriginalRelativePolynomialCharts318.cover R c)
    (into R c D) (finiteChart R c D) (infinityChart R c D) p q
    (finite_square R c D) (infinity_square R c D)
/-- Projection of the WHOLE glued quotient to the original coefficient
base. Finiteness/flatness are not inferred from its open chart pieces. -/
abbrev projection : family R c D ⟶ Spec R := into R c D ≫
  pullback.snd (ContactOriginalAffineTestCover318.p c) (ContactOriginalRelativePolynomialCharts318.baseMap R)
end ContactProjectiveQuotientGluing318
