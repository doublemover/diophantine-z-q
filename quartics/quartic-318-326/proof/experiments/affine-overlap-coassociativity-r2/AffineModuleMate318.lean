module
public import AffineModuleBaseChange318
public section
noncomputable section
namespace AffineModuleMate318
open CategoryTheory TensorProduct AffineModuleBaseChange318
open scoped ChangeOfRings
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]

lemma ring_square : (leftMap R A B).hom.comp (algebraMap R A) =
    (rightMap R A B).hom.comp (algebraMap R B) := by
  ext r
  exact (Algebra.TensorProduct.includeLeft.commutes r).trans
    (Algebra.TensorProduct.includeRight.commutes r).symm

/-- The actual restriction-of-scalars square from the literal tensor
pushout ring square. Its underlying maps are the unchanged identity maps. -/
@[expose] def restrictionSquare :
    ModuleCat.restrictScalars (rightMap R A B).hom ⋙ ModuleCat.restrictScalars (algebraMap R B) ≅
    ModuleCat.restrictScalars (leftMap R A B).hom ⋙ ModuleCat.restrictScalars (algebraMap R A) :=
  (ModuleCat.restrictScalarsComp (algebraMap R B) (rightMap R A B).hom).symm ≪≫
    ModuleCat.restrictScalarsCongr (ring_square R A B).symm ≪≫
    ModuleCat.restrictScalarsComp (algebraMap R A) (leftMap R A B).hom

/-- The canonical adjunction mate: restrict the actual covering-side unit,
use the original commuting restriction square, then take the original
extension/restriction adjunction mate. -/
@[expose] def baseChangeMap (N : ModuleCat.{u} B) :
    (pullPush R A B).obj N ⟶ (pushPull R A B).obj N :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).homEquiv _ _).symm
    ((ModuleCat.restrictScalars (algebraMap R B)).map
        ((ModuleCat.extendRestrictScalarsAdj (rightMap R A B).hom).unit.app N) ≫
      (restrictionSquare R A B).hom.app
        ((ModuleCat.extendScalars (rightMap R A B).hom).obj N))

/-- The explicit tensor comparison is the inverse of the canonical mate,
not an arbitrary isomorphism with the same source and target. -/
lemma baseChangeMap_eq (N : ModuleCat.{u} B) :
    baseChangeMap R A B N = (component R A B N).inv := by
  apply ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).homEquiv _ _).injective
  rw [baseChangeMap, Equiv.apply_symm_apply]
  ext n
  simp only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  change (1 : A ⊗[R] B) ⊗ₜ[B, (rightMap R A B).hom] n =
    ((1 : A) ⊗ₜ[R] (1 : B)) ⊗ₜ[B, (rightMap R A B).hom] n
  rw [Algebra.TensorProduct.one_def]

lemma baseChangeMap_isIso (N : ModuleCat.{u} B) : IsIso (baseChangeMap R A B N) := by
  rw [baseChangeMap_eq]
  infer_instance
end AffineModuleMate318
