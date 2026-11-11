module
public import OriginalWholeEuclideanBasis318
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public section
noncomputable section
namespace OriginalBasisDeterminantIndex318
open scoped RealInnerProductSpace
open MeasureTheory
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalFullEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalCofactorCoordinates318 OriginalWholeEuclideanBasis318
open OriginalIntegerNormalProjection318 OriginalCovolumeIndex318
set_option maxHeartbeats 4000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant in the covolume theorem is EXACTLY the integer
scalar triple product of the original controlled whole basis. -/
theorem standard_basis_determinant (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
      (((↑) : realModule p κ t → E) ∘ wholeBasis p κ t u v z hb)=
      (determinant u v z:ℝ) := by
  let b₀ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hentry (i j : Fin 3) :
      b₀.toMatrix (((↑) : realModule p κ t → E) ∘ wholeBasis p κ t u v z hb) i j=
        embed (![u,v,z] j) i := by
    rw [Basis.toMatrix_apply]
    change b₀.repr (wholeBasis p κ t u v z hb j : E) i=_
    rw [wholeBasis_apply]
    rfl
  change b₀.det _=_
  rw [Basis.det_apply,Matrix.det_fin_three]
  simp only [hentry]
  simp [embed,determinant,normal,dot] <;> ring

lemma standard_fundamental_volume :
    volume.real (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)=1 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  calc
    volume.real (ZSpan.fundamentalDomain b)=volume.real (parallelepiped b) :=
      measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b volume)
    _ = 1 := by
      rw [measureReal_def]
      have h : volume (parallelepiped b)=1 :=
        (EuclideanSpace.basisFun (Fin 3) ℝ).volume_parallelepiped
      rw [h,ENNReal.toReal_one]

/-- Exact determinant/covolume bridge for the CONSTRUCTED whole original
integer basis. This is not an appeal to rank or real independence alone. -/
theorem actual_basis_covolume (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    ZLattice.covolume (realModule p κ t)=|(determinant u v z:ℝ)| := by
  letI := actual_isZLattice p hp κ t
  have he := ZLattice.covolume_eq_det_mul_measureReal (realModule p κ t) volume
    (wholeBasis p κ t u v z hb) (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  rw [standard_basis_determinant,standard_fundamental_volume,mul_one] at he
  exact he

/-- The original odd squarefree congruence index M² is consumed at the
ACTUAL controlled basis, with no hidden power2 or finite-index factor. -/
theorem actual_basis_determinant_index (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    |(determinant u v z:ℝ)|=(FixedSquarefreeCRT318.modulus p:ℝ)^2 := by
  rw [←actual_basis_covolume p hp κ t u v z hb]
  exact original_covolume p hp hd hp2 κ t

end OriginalBasisDeterminantIndex318
