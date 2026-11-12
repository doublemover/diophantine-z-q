module
public import ContactNormalizedAbsoluteFamily318
public section
noncomputable section
namespace ContactNormalizedBoundedCartier318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "a" => ContactNormalizedAbsoluteAmbient318.base R c L hz
local notation "q" => ContactNormalizedAbsoluteFamily318.into R c L hz
local notation "N" => ContactNormalizedParameterCompact318.bound R c L hz
/-- An actual bounded original Hilbert datum, with the bound derived
from the genuine finite-flat family and finite parameter cover. -/
@[expose] def hilbert : ContactBoundedSchemeHilbertData318.Data c N a where
  ideal := q.ker
  finite := inferInstance
  flat := inferInstance
  presentation := inferInstance
  bound x := by
    rw [ClosedFamilyCanonicalProperties318.rank,ContactNormalizedAbsoluteFamily318.projection]
    exact ContactNormalizedParameterCompact318.rank_bound R c L hz x
@[expose] def data : ContactBoundedCartierEquiv318.Data c N a :=
  ⟨hilbert R c L hz,RegularClosedIso318.transport q q.ker.subschemeι
    (ClosedFamilyCanonicalProperties318.comparison q)
    (ClosedFamilyCanonicalProperties318.comparison_source q)
    (ContactNormalizedAbsoluteFamily318.regular R c L hz)⟩
/-- The old fixed-line section parameter now maps to the ACTUAL new
bounded varying-divisor parameter, not merely to a label or chosen class. -/
@[expose] def point : ContactBoundedCartierEquiv318.Point c N a :=
  ContactBoundedCartierEquiv318.equivalence c N a (data R c L hz)
@[expose] def map : ContactNormalizedSectionParameter318.scheme R c L hz ⟶
    ContactBoundedHilbertParameter318.scheme c N := (point R c L hz).val.val
@[reassoc] lemma over : map R c L hz ≫ ContactBoundedHilbertParameter318.structureMap c N=a :=
  (point R c L hz).val.property
end ContactNormalizedBoundedCartier318
