module
public import ContactCommonLaurentModule318
public import OriginalFiniteBasisBaseChange318
public import LaurentOriginalPolynomialCharts318

public section
noncomputable section
namespace ContactOriginalLaurentCoordinates318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLineBothCharts318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))
abbrev A := OriginalLaurentProjectiveOverlap318.Ring
abbrev finiteRank := Module.finrank (Polynomial ℚ) (finiteSections c L)
abbrev infinityRank := Module.finrank (Polynomial ℚ) (infinitySections c L)

/-- Base change of the original finite polynomial basis along t↦T. -/
def finiteCoordinates := OriginalFiniteBasisBaseChange318.coordinates
  OriginalLaurentProjectiveOverlap318.finiteHom (finiteSections c L)

/-- Base change of the original infinity polynomial basis along u↦T⁻¹. -/
def infinityCoordinates := OriginalFiniteBasisBaseChange318.coordinates
  OriginalLaurentProjectiveOverlap318.infinityHom (infinitySections c L)

/-- The two original polynomial coordinate systems compare through the
SAME whole-overlap Laurent module, with its actual scalar action. -/
def rawTransition : (Fin (infinityRank c L) → A) ≃ₗ[A] (Fin (finiteRank c L) → A) :=
  (infinityCoordinates c L).symm.trans
    ((ContactCommonLaurentModule318.transition c L).toLinearEquiv.trans (finiteCoordinates c L))

/-- Equality of the original two ranks is derived from the actual Laurent
comparison and invariant basis number, not assumed from a generic degree. -/
lemma rank_eq : infinityRank c L = finiteRank c L := by
  have h := (rawTransition c L).finrank_eq
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using h

/-- A single actual Laurent-linear transition for the original arbitrary
line, obtained by equality reindexing after proving the two ranks equal. -/
def transition : LaurentVectorFiltration318.V ℚ (finiteRank c L) ≃ₗ[A]
    LaurentVectorFiltration318.V ℚ (finiteRank c L) :=
  (OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L)).symm.trans (rawTransition c L)

/-- Finite Cech cokernel for the transition actually constructed from the
original line. Geometric identification with derived H1 remains separate. -/
theorem coordinate_h1_finite : FiniteDimensional ℚ (LaurentCechFinite318.H1 (transition c L)) :=
  LaurentCechFinite318.finite_h1 (transition c L)

/-- Finite matching-coordinate space for the same original transition. -/
theorem coordinate_h0_finite : FiniteDimensional ℚ
    (LaurentCechSectionsFinite318.H0 (transition c L)) :=
  LaurentCechSectionsFinite318.finite_h0 (transition c L)
end ContactOriginalLaurentCoordinates318
