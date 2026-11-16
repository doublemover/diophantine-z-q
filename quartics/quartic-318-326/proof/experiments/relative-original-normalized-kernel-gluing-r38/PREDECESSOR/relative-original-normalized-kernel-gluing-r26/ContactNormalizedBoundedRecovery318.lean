module
public import ContactNormalizedBoundedCartier318
public section
noncomputable section
namespace ContactNormalizedBoundedRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "a" => ContactNormalizedAbsoluteAmbient318.base R c L hz
local notation "q" => ContactNormalizedAbsoluteFamily318.into R c L hz
local notation "N" => ContactNormalizedParameterCompact318.bound R c L hz
local notation "x" => (ContactNormalizedBoundedCartier318.point R c L hz).val
/-- The entire previously constructed normalized effective family is
recovered as the actual universal bounded family fiber, with its original
source inclusion. No replacement by equal supports is made. -/
@[expose] def comparison : ContactNormalizedGlobalZero318.scheme R c L hz ≅
    ContactBoundedPointFamily318.family c N a x :=
  ClosedFamilyCanonicalProperties318.comparison q ≪≫
    ContactBoundedInputRecovery318.comparison c N a (ContactNormalizedBoundedCartier318.hilbert R c L hz)
@[reassoc] lemma source : (comparison R c L hz).hom ≫ ContactBoundedPointFamily318.into c N a x=q := by
  rw [comparison,Iso.trans_hom,Category.assoc,ContactBoundedInputRecovery318.comparison_source,
    ClosedFamilyCanonicalProperties318.comparison_source]
lemma full_ideal : (ContactBoundedPointFamily318.extract c N a x).ideal=q.ker :=
  ContactBoundedInputRecovery318.ideal_recovery c N a (ContactNormalizedBoundedCartier318.hilbert R c L hz)
end ContactNormalizedBoundedRecovery318
