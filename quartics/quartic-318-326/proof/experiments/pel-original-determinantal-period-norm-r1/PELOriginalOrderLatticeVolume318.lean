module
public import PELOriginalOrderNonescape318
public section
noncomputable section
open scoped BigOperators
namespace PELOriginalOrderLatticeVolume318
open PELOriginalOrderNonescape318 PELQuaternionRealRepresentation318
open PELPrincipalOrderCoordinates318
set_option maxHeartbeats 1800000

@[expose] def basisVector (g : Mat) (j : Fin 4) : Mat :=
  rightMap g (coordinatesEquiv (Pi.single j 1))

/-- Every member of the literal transported order uses INTEGER coordinates
in the transported original half-integral basis. -/
theorem coordinates_expansion (a : Coordinates) (g : Mat) :
    rightMap g (coordinatesEquiv a)=∑j:Fin 4,a j • basisVector g j := by
  have ha : a=∑j:Fin 4,a j • (Pi.single j 1 : Coordinates) := by
    funext i
    simp [Pi.single_apply]
  have h := congrArg (fun b => rightMap g (coordinatesEquiv b)) ha
  simpa only [map_sum,map_zsmul,basisVector] using h

theorem exact_integer_span (g : Mat) (M : Mat) :
    M∈lattice g ↔ ∃ a : Coordinates,M=∑j:Fin 4,a j • basisVector g j := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
    exact ⟨a,hx.symm.trans (coordinates_expansion a g)⟩
  · rintro ⟨a,ha⟩
    exact ⟨coordinatesEquiv a,(coordinates_expansion a g).trans ha.symm⟩

@[expose] def entries (M : Mat) : Fin 4 → ℝ := ![M 0 0,M 0 1,M 1 0,M 1 1]
@[expose] def basisMatrix (g : Mat) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => entries (basisVector g j) i

/-- These are the exact original real period matrices, with the original
denominators2 and10 retained. -/
theorem original_basis : basisMatrix 1=
    !![1,0,(1+beta)/2,0;
       0,-alpha,0,alpha*beta/10-alpha/2;
       0,alpha,0,alpha*beta/10+alpha/2;
       1,0,(1-beta)/2,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisMatrix,entries,basisVector,rightMap,coordinatesEquiv_value,
      representation,matrix,embed,Pi.single_apply] <;> push_cast <;> ring

/-- The signed real-coordinate determinant of the original lattice basis
is−210. This is an actual basis calculation, not a claimed Haar-measure
normalization or a substitute for a compactness theorem. -/
theorem original_basis_det : (basisMatrix 1).det= -210 := by
  rw [original_basis,Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three,Fin.sum_univ_succ,Matrix.submatrix_apply] <;>
    ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

@[expose] def rightMatrix (g : Mat) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![g 0 0,g 1 0,0,0;
     g 0 1,g 1 1,0,0;
     0,0,g 0 0,g 1 0;
     0,0,g 0 1,g 1 1]

theorem basisMatrix_transport (g : Mat) : basisMatrix g=rightMatrix g*basisMatrix 1 := by
  ext i j
  fin_cases i <;>
    simp [basisMatrix,entries,basisVector,rightMap,rightMatrix,
      Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_two] <;> ring

theorem rightMatrix_det (g : Mat) : (rightMatrix g).det=g.det^2 := by
  rw [Matrix.det_succ_row_zero,Matrix.det_fin_two]
  norm_num [rightMatrix,Matrix.det_fin_three,Fin.sum_univ_succ,Matrix.submatrix_apply] <;> ring

theorem transported_basis_det (g : Mat) : (basisMatrix g).det= -210*g.det^2 := by
  rw [basisMatrix_transport,Matrix.det_mul,rightMatrix_det,original_basis_det] <;> ring

theorem norm_one_basis_det (g : Mat) (hg : g.det=1) : (basisMatrix g).det= -210 := by
  rw [transported_basis_det,hg] <;> norm_num

/-- A single uniform nonescape package on the SAME original integer
lattices: fixed absolute coordinate determinant210 and the fixed open
entry box free of nonzero lattice vectors, for every determinant-one g. -/
theorem determinant_and_nonescape (g : Mat) (hg : g.det=1) :
    |(basisMatrix g).det|=210 ∧
      ∀ M : Mat,M∈lattice g → (∀ i j,|M i j|<(1/2:ℝ)) → M=0 := by
  refine ⟨?_,fun M hM hsmall => uniform_zero_neighborhood g hg M hM hsmall⟩
  rw [norm_one_basis_det g hg] <;> norm_num
end PELOriginalOrderLatticeVolume318
