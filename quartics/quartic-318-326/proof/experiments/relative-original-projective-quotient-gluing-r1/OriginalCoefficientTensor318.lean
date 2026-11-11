module
public import RelativeCoefficientChange318
public import TensorPushoutModule318
public import ScalarExtensionTensor318
public section
noncomputable section
namespace OriginalCoefficientTensor318
open AlgebraicGeometry CategoryTheory TensorProduct
open scoped TensorProduct ChangeOfRings
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (k R S B : CommRingCat.{u}) [Algebra k R] [Algebra k S] [Algebra k B]
  (f : R →ₐ[k] S)
local instance : Algebra R S := f.toAlgebra
local instance : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' (by
  ext a
  exact (f.commutes a).symm)
abbrev oldRing := CommRingCat.of (R ⊗[k] B)
abbrev newRing := CommRingCat.of (S ⊗[k] B)
abbrev pushout := CommRingCat.of (S ⊗[R] (R ⊗[k] B))
local instance : Algebra (oldRing k R B) (newRing k S B) :=
  (RelativeCoefficientChange318.ringMap k R S B f).hom.toAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The coefficient tensor square is an actual ring pushout; its
normalization fixes S and the complete old chart, not a chosen basis. -/
@[expose] def ringEquivalence : pushout k R S B f ≃ₐ[S] newRing k S B :=
  Algebra.TensorProduct.cancelBaseChange k R S S B

lemma ringEquivalence_right (t : oldRing k R B) :
    ringEquivalence k R S B f ((1 : S) ⊗ₜ[R] t) =
      RelativeCoefficientChange318.ringMap k R S B f t := by
  induction t using TensorProduct.inductionOn with
  | tmul r b =>
      simp [ringEquivalence,RelativeCoefficientChange318.ringMap_tmul,Algebra.smul_def]
  | add x y hx hy => simp only [tmul_add,map_add,hx,hy]

/-- The same ring isomorphism is linear for the ACTUAL old chart map. -/
@[expose] def rightEquivalence : pushout k R S B f ≃ₗ[oldRing k R B] newRing k S B where
  __ := (ringEquivalence k R S B f).toAddEquiv
  map_smul' t z := by
    change ringEquivalence k R S B f
      (((1 : S) ⊗ₜ[R] t) * z) =
        RelativeCoefficientChange318.ringMap k R S B f t * ringEquivalence k R S B f z
    rw [map_mul,ringEquivalence_right]

variable (N : ModuleCat.{u} (oldRing k R B))
local instance : Module R N := Module.compHom N (algebraMap R (oldRing k R B))
local instance : IsScalarTower R (oldRing k R B) N := IsScalarTower.of_compHom ..

/-- Transport along the actual ring pushout, preserving both old-chart
balancing and the independent S action. -/
@[expose] def tensorTransport :
    pushout k R S B f ⊗[oldRing k R B] N ≃ₗ[S] newRing k S B ⊗[oldRing k R B] N := by
  let e := TensorProduct.congr (rightEquivalence k R S B f) (LinearEquiv.refl _ N)
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro s z
  induction z using TensorProduct.inductionOn with
  | tmul t n =>
      change ringEquivalence k R S B f (s • t) ⊗ₜ[oldRing k R B] n =
        s • (ringEquivalence k R S B f t ⊗ₜ[oldRing k R B] n)
      rw [(ringEquivalence k R S B f).toLinearEquiv.map_smul,smul_tmul']
  | add x y hx hy =>
      change e (s • x) = s • e x at hx
      change e (s • y) = s • e y at hy
      change e (s • (x+y)) = s • e (x+y)
      simp only [smul_add,map_add,hx,hy]

/-- Actual chart-ring extension reduces to coefficient-only extension,
with no flatness, finite-free chart, or line trivialization hypothesis. -/
@[expose] def tensorEquivalence :
    newRing k S B ⊗[oldRing k R B] N ≃ₗ[S] S ⊗[R] N :=
  (tensorTransport k R S B f N).symm.trans
    (TensorPushoutModule318.equivalence R S (oldRing k R B) N)

lemma tensorEquivalence_symm_tmul (s : S) (n : N) :
    (tensorEquivalence k R S B f N).symm (s ⊗ₜ[R] n) =
      (s ⊗ₜ[k] (1 : B)) ⊗ₜ[oldRing k R B] n := by
  change ringEquivalence k R S B f (s ⊗ₜ[R] (1 : oldRing k R B)) ⊗ₜ[oldRing k R B] n = _
  rw [show (1 : oldRing k R B) = (1 : R) ⊗ₜ[k] (1 : B) from rfl]
  simp only [ringEquivalence,Algebra.TensorProduct.cancelBaseChange_tmul,one_smul]

/-- Categorical scalar extension with its precise original ring map,
not an extension along a newly inferred map. -/
@[expose] def categoricalEquivalence :
    (ModuleCat.restrictScalars (algebraMap S (newRing k S B))).obj
      ((ModuleCat.extendScalars (RelativeCoefficientChange318.ringMap k R S B f).hom).obj N)
        ≃ₗ[S] S ⊗[R] N := by
  let e := ScalarExtensionTensor318.tensorEquiv (S := oldRing k R B)
    (T := newRing k S B) N
  let eS :
      (ModuleCat.restrictScalars (algebraMap S (newRing k S B))).obj
        ((ModuleCat.extendScalars (RelativeCoefficientChange318.ringMap k R S B f).hom).obj N)
          ≃ₗ[S] newRing k S B ⊗[oldRing k R B] N :=
    { e.toAddEquiv with
      map_smul' := by
        intro s n
        change e (algebraMap S (newRing k S B) s • n) = s • e n
        rw [e.map_smul,IsScalarTower.algebraMap_smul] }
  exact eS.trans (tensorEquivalence k R S B f N)
lemma categoricalEquivalence_symm_tmul (s : S) (n : N) :
    (categoricalEquivalence k R S B f N).symm (s ⊗ₜ[R] n) =
      (s ⊗ₜ[k] (1 : B)) ⊗ₜ[oldRing k R B,
        (RelativeCoefficientChange318.ringMap k R S B f).hom] n := by
  change (ScalarExtensionTensor318.tensorEquiv (S := oldRing k R B)
    (T := newRing k S B) N).symm
      ((tensorEquivalence k R S B f N).symm (s ⊗ₜ[R] n)) = _
  rw [tensorEquivalence_symm_tmul]
  rfl
end OriginalCoefficientTensor318
