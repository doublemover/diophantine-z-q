module

public import QuaternionicRealPeriod318
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

public section
noncomputable section

open QuaternionicRealPeriod318
open scoped BigOperators Matrix

namespace SelectedActualPELPeriodColumns318

abbrev R4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev C2 := Matrix (Fin 2) (Fin 2) ℂ

-- Source and target each have a specified, DIFFERENT grouped ordering.
def flatten (A : RealMatrices) : Fin 4 → ℝ := ![A 0 0, A 1 0, A 0 1, A 1 1]

def grouped (z : ComplexVectors) : Fin 4 → ℝ := ![(z 0).re, (z 1).re, (z 0).im, (z 1).im]

def basisMatrix (β : Fin 4 → RealMatrices) : R4 := fun i j => flatten (β j) i

/-- T on the literal integral order S in the fixed real splitting. -/
def orderT (S : Submodule ℤ RealMatrices) (b : Module.Basis (Fin 4) ℤ S) : R4 :=
  basisMatrix (fun j => (b j : RealMatrices))

def Bτ (τ : ℂ) : R4 :=
  !![τ.re,0,1,0; 0,τ.re,0,1; τ.im,0,0,0; 0,τ.im,0,0]

theorem standard_period_coordinates (τ : ℂ) (A : RealMatrices) :
    grouped (period τ A) = (Bτ τ).mulVec (flatten A) := by
  funext i
  fin_cases i <;> simp [grouped, period, row, Bτ, flatten, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring

/-- The denominator and argument of the genuine real Möbius coordinate
change. A right change of an order element acts before evaluation, unlike
left quaternion multiplication on the tangent. -/
def chartDen (g : RealMatrices) (τ : ℂ) : ℂ := (g 1 0 : ℂ) * τ + (g 1 1 : ℂ)

def chartMove (g : RealMatrices) (τ : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * τ + (g 0 1 : ℂ)) / chartDen g τ

/-- Exact deck-coordinate transport across the change of representative.
Replacing β by β g⁻¹ in an overlapping marked chart scales the lattice
by the corresponding common complex scalar, not by an integral index. -/
theorem right_chart_period (β g : RealMatrices) (τ : ℂ) (h : chartDen g τ ≠ 0) :
    period τ (β * g) = chartDen g τ • period (chartMove g τ) β := by
  funext i
  simp only [period, row, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_add, Complex.ofReal_mul, chartMove]
  field_simp [h]
  simp only [chartDen]
  ring

/-- X has columns equal to the actual h_j in dz_i; evaluating
h_j on a column of periods is Xᵀ, NOT X^* and NOT X. -/
def RX (X : C2) : R4 :=
  !![(X 0 0).re,(X 1 0).re,-(X 0 0).im,-(X 1 0).im;
     (X 0 1).re,(X 1 1).re,-(X 0 1).im,-(X 1 1).im;
     (X 0 0).im,(X 1 0).im, (X 0 0).re, (X 1 0).re;
     (X 0 1).im,(X 1 1).im, (X 0 1).re, (X 1 1).re]

theorem coframe_period_coordinates (X : C2) (z : ComplexVectors) :
    grouped (X.transpose.mulVec z) = (RX X).mulVec (grouped z) := by
  funext i
  fin_cases i <;> simp [grouped, RX, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    Fin.sum_univ_succ, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im] <;> ring

def coframedPeriods (τ : ℂ) (X : C2) (β : Fin 4 → RealMatrices) : R4 :=
  fun i j => grouped (X.transpose.mulVec (period τ (β j))) i

/-- Exact column equality consumes the same β's, not a new T
picked only to match a determinant. -/
theorem coframedPeriods_eq (τ : ℂ) (X : C2) (β : Fin 4 → RealMatrices) :
    coframedPeriods τ X β = ((RX X) * (Bτ τ)) * basisMatrix β := by
  ext i j
  change grouped (X.transpose.mulVec (period τ (β j))) i =
    (((RX X) * (Bτ τ)).mulVec (flatten (β j))) i
  rw [coframe_period_coordinates, standard_period_coordinates, Matrix.mulVec_mulVec]

/-- Exact image result for the complete integral lattice. The hypothesis
is the pointwise kernel equality of the original quotient chart (Yuan
§4.2); it is not finite-index inclusion or an arch norm equation. -/
theorem full_period_columns {J : Type*} [AddCommGroup J]
    (τ : ℂ) (S : Submodule ℤ RealMatrices) (b : Module.Basis (Fin 4) ℤ S)
    (q : ComplexVectors →+ J)
    (hActual : ∀ z, q z = 0 ↔ ∃ A : S, period τ (A : RealMatrices) = z)
    (z : ComplexVectors) :
    q z = 0 ↔ ∃ c : Fin 4 → ℤ,
      (∑ j : Fin 4, c j • period τ (b j : RealMatrices)) = z := by
  rw [hActual]
  constructor
  · rintro ⟨A,rfl⟩
    refine ⟨fun j => b.repr A j,?_⟩
    have h := congrArg (fun C : S => period τ (C : RealMatrices)) (b.sum_repr A)
    change period τ (S.subtype (∑ i, b.repr A i • b i)) = _ at h
    simpa only [map_sum, map_zsmul, Submodule.subtype_apply] using h
  · rintro ⟨c,rfl⟩
    refine ⟨∑ j, c j • b j,?_⟩
    change period τ (S.subtype (∑ i, c i • b i)) = _
    simp only [map_sum, map_zsmul, Submodule.subtype_apply]

/-- Main involution in the SAME split-real algebra is adjugate. -/
def adj (A : RealMatrices) : RealMatrices := !![A 1 1,-A 0 1; -A 1 0,A 0 0]

def G : R4 := !![0,0,0,-1; 0,0,1,0; 0,1,0,0; -1,0,0,0]

/-- Left multiplication by ν=μ⁻¹ in column-grouped coordinates. -/
def leftBlock (ν : RealMatrices) : R4 :=
  !![ν 0 0,ν 0 1,0,0; ν 1 0,ν 1 1,0,0; 0,0,ν 0 0,ν 0 1; 0,0,ν 1 0,ν 1 1]

theorem leftBlock_coordinates (ν A : RealMatrices) :
    (leftBlock ν).mulVec (flatten A) = flatten (ν * A) := by
  funext i
  fin_cases i <;> simp [leftBlock, flatten, Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_succ]

theorem leftBlock_basis (ν : RealMatrices) (β : Fin 4 → RealMatrices) :
    leftBlock ν * basisMatrix β = basisMatrix (fun j => ν * β j) := by
  ext i j
  change ((leftBlock ν).mulVec (flatten (β j))) i = flatten (ν * β j) i
  rw [leftBlock_coordinates]

theorem trace_pairing_coordinates (A B : RealMatrices) :
    (∑ i : Fin 4, ((∑ k : Fin 4, flatten A k * G k i) * flatten B i)) =
      -(Matrix.trace (A * adj B)) := by
  simp [flatten, G, adj, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Full entrywise signed Riemann form on the same order basis. This
is a matrix identity, not an equality between chosen covolumes. -/
theorem polarization_gram (ν : RealMatrices) (β : Fin 4 → RealMatrices) :
    (((leftBlock ν) * basisMatrix β).transpose * G) * basisMatrix β =
      fun i j => -(Matrix.trace ((ν * β i) * adj (β j))) := by
  rw [leftBlock_basis]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, basisMatrix]
  exact trace_pairing_coordinates (ν * β i) (β j)

/-- Retain any genuine integer Gram already recorded on this lattice;
realification cannot change or rescale its entries. -/
theorem compare_integral_gram (ν : RealMatrices) (β : Fin 4 → RealMatrices)
    (Eℤ : Matrix (Fin 4) (Fin 4) ℤ)
    (h : ∀ i j, (Eℤ i j : ℝ) = -(Matrix.trace ((ν * β i) * adj (β j)))) :
    (((leftBlock ν) * basisMatrix β).transpose * G) * basisMatrix β =
      Eℤ.map (Int.castRingHom ℝ) := by
  rw [polarization_gram]
  ext i j
  exact (h i j).symm

end SelectedActualPELPeriodColumns318

#print axioms SelectedActualPELPeriodColumns318.coframedPeriods_eq
#print axioms SelectedActualPELPeriodColumns318.full_period_columns
#print axioms SelectedActualPELPeriodColumns318.compare_integral_gram

#print axioms SelectedActualPELPeriodColumns318.right_chart_period
