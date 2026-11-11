module
public import ContactRelativeOriginalHZero318
public import KernelComparisonTransport318
public import ContactCoefficientCechBaseChange318
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public section
noncomputable section
namespace ContactRelativeHZeroBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open scoped TensorProduct
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance : Module S (originalSections S c (L' R S f c L)) := overlapModule S c _
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module S Γ((L' R S f c L).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c)
    (L' R S f c L) ⊤

@[expose] def pairEquivalence : S ⊗[R] (finiteSections R c L × infinitySections R c L) ≃ₗ[S]
    (finiteSections S c (L' R S f c L) × infinitySections S c (L' R S f c L)) :=
  (TensorProduct.prodRight R S S (finiteSections R c L) (infinitySections R c L)).trans
    ((finiteEquivalence R S f c L).prodCongr (infinityEquivalence R S f c L))

lemma pair_tmul (s : S) (x : finiteSections R c L × infinitySections R c L) :
    pairEquivalence R S f c L (s ⊗ₜ[R] x) =
      (finiteEquivalence R S f c L (s ⊗ₜ[R] x.1),
        infinityEquivalence R S f c L (s ⊗ₜ[R] x.2)) := by
  rw [pairEquivalence,LinearEquiv.trans_apply,TensorProduct.prodRight_tmul]
  rfl

/-- The full genuine Cech DIFFERENCE square, with both original
restriction maps and the genuine coefficient comparison on each chart. -/
lemma difference_square :
    (ContactRelativeCechProjective318.difference S c (L' R S f c L)).comp
      (pairEquivalence R S f c L).toLinearMap =
    (overlapEquivalence R S f c L).toLinearMap.comp
      ((ContactRelativeCechProjective318.difference R c L).baseChange S) := by
  apply AlgebraTensorModule.ext
  intro s x
  have h0 := LinearMap.congr_fun (ContactCoefficientCechBaseChange318.finite_square R S f c L)
    (s ⊗ₜ[R] x.1)
  have h1 := LinearMap.congr_fun (ContactCoefficientCechBaseChange318.infinity_square R S f c L)
    (s ⊗ₜ[R] x.2)
  simp only [LinearMap.comp_apply,LinearMap.baseChange_tmul] at h0 h1
  change ContactRelativeCechProjective318.difference S c (L' R S f c L)
    (pairEquivalence R S f c L (s ⊗ₜ[R] x)) =
      overlapEquivalence R S f c L (s ⊗ₜ[R]
        ContactRelativeCechProjective318.difference R c L x)
  rw [pair_tmul]
  change _-_ = overlapEquivalence R S f c L (s ⊗ₜ[R] (_-_))
  rw [tmul_sub,map_sub,h0,h1]

@[expose] def comparedKernel :
    LinearMap.ker ((ContactRelativeCechProjective318.difference R c L).baseChange S) ≃ₗ[S]
      LinearMap.ker (ContactRelativeCechProjective318.difference S c (L' R S f c L)) :=
  KernelComparisonTransport318.equivalence _ _ (pairEquivalence R S f c L)
    (overlapEquivalence R S f c L) (difference_square R S f c L)

variable (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L, x=0)

/-- Actual H1 vanishing supplies the splitting; no flatness of R→S is
assumed. The resulting H0 comparison uses the original chart section maps. -/
@[expose] def kernelEquivalence :
    S ⊗[R] LinearMap.ker (ContactRelativeCechProjective318.difference R c L) ≃ₗ[S]
      LinearMap.ker (ContactRelativeCechProjective318.difference S c (L' R S f c L)) := by
  let s := Classical.choose (ContactRelativeCechProjective318.split_kernel R c L hz).1
  have hs := Classical.choose_spec (ContactRelativeCechProjective318.split_kernel R c L hz).1
  exact (SplitKernelBaseChange318.equivalence R _ _
    (ContactRelativeCechProjective318.difference R c L) s hs S).trans
      (comparedKernel R S f c L)

/-- Genuine original global sections commute with every coefficient
extension on the actual H1-vanishing locus. Both structural coefficient
actions and the actual pulled original line are retained. No claim of
unconditional H0 base change, finite generation or a finite complex. -/
@[expose] def equivalence : S ⊗[R] Γ(L.object,⊤) ≃ₗ[S] Γ((L' R S f c L).object,⊤) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl S S)
    (ContactRelativeOriginalHZero318.equivalence R c L)).trans
      ((kernelEquivalence R S f c L hz).trans
        (ContactRelativeOriginalHZero318.equivalence S c (L' R S f c L)).symm)
/-- The global-section comparison has the ACTUAL coefficient-pullback
coordinates on both original charts. Thus its forward map does not depend
on the chosen splitting used only to prove tensor-kernel bijectivity. -/
lemma coordinates (s : S) (x : Γ(L.object,⊤)) :
    ContactRelativeOriginalHZero318.pair S c (L' R S f c L)
      (equivalence R S f c L hz (s ⊗ₜ[R] x)) =
    pairEquivalence R S f c L
      (s ⊗ₜ[R] ContactRelativeOriginalHZero318.pair R c L x) := by
  change ContactRelativeOriginalHZero318.pair S c (L' R S f c L)
    ((ContactRelativeOriginalHZero318.equivalence S c (L' R S f c L)).symm _) = _
  rw [ContactRelativeOriginalHZero318.pair_symm]
  rfl
end ContactRelativeHZeroBaseChange318
