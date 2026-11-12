module
public import ContactRelativeGlobalCoordinateBounds318
public import FinitePolynomialWindowRetract318
public section
noncomputable section
namespace ContactRelativeFiniteProjectiveHZero318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : IsScalarTower ℚ (Polynomial ℚ) (finiteRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : IsScalarTower ℚ (Polynomial ℚ) (infinityRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : Module.Finite (Polynomial ℚ) (finiteRing c) :=
  (ContactKummerOrder318.source_finite_free c).1
local instance : Module.Free (Polynomial ℚ) (finiteRing c) :=
  (ContactKummerOrder318.source_finite_free c).2
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : IsScalarTower R (Polynomial R) (finiteSections R c L) := IsScalarTower.of_compHom ..
local instance : IsScalarTower R (Polynomial R) (infinitySections R c L) := IsScalarTower.of_compHom ..
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤

/-- Actual H0 is FINITE projective on the original H1-vanishing locus.
The actual split Cech retraction and both original polynomial retracts
are restricted to finite coefficient windows whose bounds are produced
from the opposite chart, rather than assumed for unknown global sections. -/
theorem finite_projective (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L, x=0) :
    Module.Finite R Γ(L.object,⊤) ∧ Module.Projective R Γ(L.object,⊤) := by
  obtain ⟨r,out0,back0,h0⟩ := RelativePolynomialChartProjective318.sections_retract R
    (finiteRing c) (finiteLine R c L)
  obtain ⟨s,out1,back1,h1⟩ := RelativePolynomialChartProjective318.sections_retract R
    (infinityRing c) (infinityLine R c L)
  obtain ⟨σ,hσ⟩ := (ContactRelativeCechProjective318.split_kernel R c L hz).1
  let e := ContactRelativeOriginalHZero318.equivalence R c L
  let outPair := (out0.restrictScalars R).prodMap (out1.restrictScalars R)
  let backPair := (back0.restrictScalars R).prodMap (back1.restrictScalars R)
  let out := outPair.comp (ContactRelativeOriginalHZero318.pair R c L)
  let back := e.symm.toLinearMap.comp
    ((SplitKernelBaseChange318.retraction R _ _ (ContactRelativeCechProjective318.difference R c L) σ hσ).comp backPair)
  have hpair (x : finiteSections R c L × infinitySections R c L) : backPair (outPair x) = x := by
    apply Prod.ext
    · exact LinearMap.congr_fun h0 x.1
    · exact LinearMap.congr_fun h1 x.2
  have hsplit : back.comp out = LinearMap.id := by
    ext x
    change e.symm (SplitKernelBaseChange318.retraction R _ _
      (ContactRelativeCechProjective318.difference R c L) σ hσ
      (backPair (outPair (ContactRelativeOriginalHZero318.pair R c L x)))) = x
    rw [hpair]
    change e.symm (SplitKernelBaseChange318.retraction R _ _
      (ContactRelativeCechProjective318.difference R c L) σ hσ (e x)) = x
    rw [SplitKernelBaseChange318.retract,LinearEquiv.symm_apply_apply]
  obtain ⟨b,hb⟩ := ContactRelativeGlobalCoordinateBounds318.finite_bound R c L out0
  obtain ⟨d,hd⟩ := ContactRelativeGlobalCoordinateBounds318.infinity_bound R c L out1
  exact FinitePolynomialWindowRetract318.finite_projective R Γ(L.object,⊤)
    r s out back hsplit b d hb hd

/-- Finite presentation here is a consequence of a genuine finite free
retract, and is asserted ONLY on the proved H1-vanishing locus. -/
theorem finitePresentation (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L, x=0) :
    Module.FinitePresentation R Γ(L.object,⊤) := by
  letI := (finite_projective R c L hz).1
  letI := (finite_projective R c L hz).2
  exact Module.finitePresentation_of_projective R Γ(L.object,⊤)
end ContactRelativeFiniteProjectiveHZero318
