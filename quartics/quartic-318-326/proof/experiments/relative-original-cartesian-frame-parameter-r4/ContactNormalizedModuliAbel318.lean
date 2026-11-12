module
public import ContactCartierFamilyYoneda318
public import ContactPositiveBoundedPresentation318
public section
noncomputable section
namespace ContactNormalizedModuliAbel318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "a" => ContactNormalizedAbsoluteAmbient318.base R c L hz
local notation "N" => ContactNormalizedParameterCompact318.bound R c L hz
local notation "D" => ContactNormalizedBoundedCartier318.data R c L hz
/-- Actual normalized section families now factor through the genuine
moduli presheaf with their internally produced bound. -/
@[expose] def family : yoneda.obj (Over.mk a) ⟶ ContactCartierDataPresheaf318.presheaf c N :=
  ContactCartierFamilyYoneda318.family c N a D
lemma abel : family R c L hz ≫ ContactCartierUniversalAbel318.transformation c N=
    ContactBoundedCartierAbel318.transformation c N a D :=
  ContactCartierFamilyYoneda318.abel c N a D
lemma parameter (T : Over (Spec (CommRingCat.of ℚ))) (f : T ⟶ Over.mk a) :
    ((ContactCartierPointPresheaf318.inclusion c N).app (Opposite.op T)
      ((ContactCartierPresheafEquiv318.equivalence c N).hom.app (Opposite.op T)
        ((family R c L hz).app (Opposite.op T) f))).left=
      f.left ≫ ContactNormalizedBoundedCartier318.map R c L hz :=
  ContactCartierFamilyYoneda318.parameter c N a D T f
end ContactNormalizedModuliAbel318
