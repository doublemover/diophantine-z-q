module
public import CartierAmbientIso318
public section
noncomputable section
namespace ContactNormalizedBoundedDivisor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactNormalizedGlobalClosedFamily318.into R c L hz
local notation "q" => ContactNormalizedAbsoluteFamily318.into R c L hz
local notation "e" => ContactNormalizedAbsoluteAmbient318.comparison R c L hz
local notation "a" => ContactNormalizedAbsoluteAmbient318.base R c L hz
local notation "N" => ContactNormalizedParameterCompact318.bound R c L hz
local notation "D" => ContactNormalizedBoundedCartier318.data R c L hz
/-- The genuine bounded original divisor line, transported through the
proved literal ambient comparison, on the original normalized family. -/
@[expose] def line : Line (ContactNormalizedGlobalClosedFamily318.ambient R c L hz) :=
  LineSheafPullback318.line e.hom (ContactBoundedCartierAbel318.divisorLine c N a D)
lemma canonical_class : classOf (ContactBoundedCartierAbel318.divisorLine c N a D)=
    classOf (CartierCanonicalSection318.divisorLine q (ContactNormalizedAbsoluteFamily318.regular R c L hz)) :=
  (RegularClosedKernelTransport318.dual_class q q.ker.subschemeι
    (ClosedFamilyCanonicalProperties318.comparison q)
    (ClosedFamilyCanonicalProperties318.comparison_source q)
    (ContactNormalizedAbsoluteFamily318.regular R c L hz) D.property).symm
/-- The bounded classifier carries the SAME original normalized O(D),
not an independently chosen line in an equal abstract Picard class. -/
lemma original_class : classOf (line R c L hz)=
    classOf (ContactNormalizedGlobalIdealLine318.divisorLine R c L hz) := by
  change LineSheafPullback318.pullback e.hom
    (classOf (ContactBoundedCartierAbel318.divisorLine c N a D))=_
  rw [canonical_class]
  exact CartierAmbientIso318.pulled_class p e (ContactNormalizedGlobalCartier318.regular_charts R c L hz)
@[expose] def originalIso : (line R c L hz).object ≅
    (ContactNormalizedGlobalIdealLine318.divisorLine R c L hz).object :=
  Classical.choice ((classOf_eq_iff _ _).mp (original_class R c L hz))
end ContactNormalizedBoundedDivisor318
