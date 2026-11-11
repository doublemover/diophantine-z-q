module
public import CyclicWordNormalization318
public import Mathlib.Data.Matrix.Basic
public section
noncomputable section
open scoped Matrix
namespace CyclicNormalizationMatrixFormula318
open FreeQuotientFramedClassifier318 CyclicWordNormalization318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
variable (d : Framed R A ι) (w : ι → A) (h : IsUnit (columns R A ι d w).det)

lemma action_matrix (a : A) :
    LinearMap.toMatrixAlgEquiv' ((normalize R A ι d w h).action a)=
      (columns R A ι d w)⁻¹ * LinearMap.toMatrixAlgEquiv' (d.action a) *
        columns R A ι d w := by
  ext i j
  rw [LinearMap.toMatrixAlgEquiv'_apply]
  change ((columns R A ι d w)⁻¹ *ᵥ
    (d.action a (columns R A ι d w *ᵥ Pi.single j 1))) i=_
  rw [← LinearMap.toMatrix'_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec_single_one,Matrix.col_apply]

lemma marked_vector : (normalize R A ι d w h).marked=
    (columns R A ι d w)⁻¹ *ᵥ d.marked := rfl

section Coefficients
variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- Inversion commutes with arbitrary coefficient maps on the unit-determinant
locus, including maps to rings with nilpotents. -/
lemma inverse_map (M : Matrix ι ι S) (hM : IsUnit M.det) :
    f.mapMatrix M⁻¹=(f.mapMatrix M)⁻¹ := by
  have hleft : f.mapMatrix M⁻¹ * f.mapMatrix M=1 := by
    rw [← map_mul,Matrix.nonsing_inv_mul M hM,map_one]
  have hu : IsUnit (f.mapMatrix M).det :=
    Matrix.isUnit_det_of_left_inverse hleft
  calc
    f.mapMatrix M⁻¹=f.mapMatrix M⁻¹ * 1 := (mul_one _).symm
    _=f.mapMatrix M⁻¹ * (f.mapMatrix M * (f.mapMatrix M)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hu]
    _=(f.mapMatrix M⁻¹ * f.mapMatrix M) * (f.mapMatrix M)⁻¹ := (mul_assoc _ _ _).symm
    _=(f.mapMatrix M)⁻¹ := by rw [hleft,one_mul]

lemma mulVec_map (M : Matrix ι ι S) (x : ι → S) (i : ι) :
    f ((M *ᵥ x) i)=(f.mapMatrix M *ᵥ (fun j => f (x j))) i := by
  change f (∑ j, M i j * x j)=∑ j, f (M i j) * f (x j)
  simp only [map_sum,map_mul]
end Coefficients
end CyclicNormalizationMatrixFormula318
