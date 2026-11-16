module
public import OriginalLineMayerVietorisQuotient318
public import CohomologyRationalScalar318
public import ModuleScalar318
public import Mathlib.Algebra.Module.LinearMap.Rat
public section
noncomputable section
namespace OriginalLineRationalCohomology318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open OriginalLineRestrictionAdditive318 NormalizedStructureTrace318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℚ)) (L : Line X)

/-- Rational coefficients act on the unchanged original module sections
through the original structure-map ring homomorphism on this open. -/
@[expose,reducible] def sectionModule (U : X.Opens) : Module ℚ Γ(L.object,U) :=
  Module.compHom Γ(L.object,U) (scalar p U)

/-- The SAME existing module-scalar endomorphism, forgotten to the actual
additive coefficient sheaf. This precedes all cohomology or coordinates. -/
def multiply (a : ℚ) : additive L ⟶ additive L :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map
    (ModuleScalar318.map L.object (scalar p ⊤ a))

lemma multiply_apply (a : ℚ) (U : X.Opens) (s : Γ(L.object,U)) :
    (multiply p L a).hom.app (op U) s = scalar p U a • s := by
  change (ModuleScalar318.map L.object (scalar p ⊤ a)).app U s = _
  rw [ModuleScalar318.map_apply,scalar_restrict]

lemma multiply_zero : multiply p L 0 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change (multiply p L 0).hom.app U s = 0
  rw [multiply_apply,map_zero,zero_smul]
lemma multiply_one : multiply p L 1 = 𝟙 _ := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change (multiply p L 1).hom.app U s = s
  rw [multiply_apply,map_one,one_smul]
lemma multiply_add (a b : ℚ) : multiply p L (a+b) = multiply p L a + multiply p L b := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change (multiply p L (a+b)).hom.app U s =
    (multiply p L a).hom.app U s + (multiply p L b).hom.app U s
  rw [multiply_apply,multiply_apply,multiply_apply,map_add,add_smul]
lemma multiply_mul (a b : ℚ) : multiply p L (a*b) = multiply p L b ≫ multiply p L a := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change (multiply p L (a*b)).hom.app U s =
    (multiply p L a).hom.app U ((multiply p L b).hom.app U s)
  rw [multiply_apply,multiply_apply,multiply_apply,map_mul,mul_smul]

/-- Genuine rational action on the unchanged ORIGINAL derived Ext carrier,
induced by the actual coefficient endomorphism. No quotient or coordinate
equivalence is used to manufacture a vector-space structure. -/
@[expose,reducible] def cohomologyModule (n : ℕ) : Module ℚ (Sheaf.H (additive L) n) :=
  CohomologyRationalScalar318.ofAction (additive L) (multiply p L)
    (multiply_zero p L) (multiply_one p L) (multiply_add p L) (multiply_mul p L) n

lemma cohomology_smul (n : ℕ) (a : ℚ) (x : Sheaf.H (additive L) n) :
    letI := cohomologyModule p L n
    a • x = Sheaf.H.map (multiply p L a) n x := rfl

variable [IsIntegral X]

/-- The original derived boundary is linear for the already constructed
structural actions: additive maps between rational modules are linear. -/
@[expose] def boundaryLinear (U V : X.Opens) (h : U ⊔ V = ⊤) :
    letI := sectionModule p L (U ⊓ V)
    letI := cohomologyModule p L 1
    Γ(L.object,U ⊓ V) →ₗ[ℚ] OriginalLineMayerVietorisQuotient318.H1 L := by
  letI := sectionModule p L (U ⊓ V)
  letI := cohomologyModule p L 1
  exact (OriginalLineMayerVietorisQuotient318.boundary L U V h).toRatLinearMap

/-- Explicit original coefficient naturality, with scalar multiplication
identified on BOTH the actual section and original derived cohomology. -/
lemma boundary_scalar (U V : X.Opens) (h : U ⊔ V = ⊤) (a : ℚ)
    (s : Γ(L.object,U ⊓ V)) :
    OriginalLineMayerVietorisQuotient318.boundary L U V h
      (scalar p (U ⊓ V) a • s) =
    Sheaf.H.map (multiply p L a) 1
      (OriginalLineMayerVietorisQuotient318.boundary L U V h s) := by
  letI := sectionModule p L (U ⊓ V)
  letI := cohomologyModule p L 1
  exact (boundaryLinear p L U V h).map_smul a s
end OriginalLineRationalCohomology318
