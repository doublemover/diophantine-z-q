module
public import ContactFieldLinearSectionParameter318
public import ProjectiveSymmetricSmooth318
public import FiniteProjectiveDualRetract318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace ContactFieldLinearSectionSmooth318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactFieldLinearSectionParameter318
variable (K : Type) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
  (L : Line (curve (CommRingCat.of K) c))
local notation "R" => CommRingCat.of K
local instance : Module K Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite K Γ(L.object,⊤) := ContactFieldSectionBaseChange318.finite K c L
local instance : Module.Projective K Γ(L.object,⊤) := inferInstance

instance algebra_smooth : Algebra.Smooth K (ring K c L) := by
  let F := FiniteProjectiveEvaluationFrame318.frame K Γ(L.object,⊤)
  letI : Module.Finite K (Module.Dual K Γ(L.object,⊤)) :=
    (FiniteProjectiveDualRetract318.properties K Γ(L.object,⊤) F).1
  letI : Module.Projective K (Module.Dual K Γ(L.object,⊤)) :=
    (FiniteProjectiveDualRetract318.properties K Γ(L.object,⊤) F).2
  exact ProjectiveSymmetricSmooth318.smooth K (Module.Dual K Γ(L.object,⊤))

abbrev projection : scheme K c L ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ring K c L)))
/-- Genuine smoothness of the actual H0 linear parameter for a line
DESCENDED FROM A FIELD, including lines with nonzero H1. No smoothness
of arbitrary varying-line kernel parameters is inferred. -/
instance smooth : Smooth (projection K c L) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr inferInstance
end ContactFieldLinearSectionSmooth318
