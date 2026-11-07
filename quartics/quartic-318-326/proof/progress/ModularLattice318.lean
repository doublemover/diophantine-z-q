module
public import EllipticTorsion318
public import ModularCurveChange318
public section
noncomputable section
open scoped MatrixGroups
open PeriodEisenstein318 UpperHalfPlane
namespace ModularLattice318
set_option maxHeartbeats 0

@[expose] def d (g : SL(2,ℤ)) (tau : UpperHalfPlane) : ℂ :=
  (g 1 0:ℂ)*tau+(g 1 1:ℂ)

lemma d_eq_denom (g : SL(2,ℤ)) (tau : UpperHalfPlane) :
    d g tau=denom ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) tau := by
  simp [d,denom,Matrix.SpecialLinearGroup.mapGL]

lemma d_ne_zero (g : SL(2,ℤ)) (tau : UpperHalfPlane) : d g tau≠0 := by
  rw [d_eq_denom]
  exact denom_ne_zero _ tau

lemma action_formula (g : SL(2,ℤ)) (tau : UpperHalfPlane) :
    ((g•tau:UpperHalfPlane):ℂ)=((g 0 0:ℂ)*tau+(g 0 1:ℂ))/d g tau := by
  simpa [d] using coe_specialLinearGroup_apply g tau

lemma determinant_one (g : SL(2,ℤ)) :
    (g 0 0:ℂ)*(g 1 1:ℂ)-(g 0 1:ℂ)*(g 1 0:ℂ)=1 := by
  have hh := g.property
  rw [Matrix.det_fin_two] at hh
  exact_mod_cast hh

/-- The exact change of integer period coordinates in the forward direction. -/
lemma period_forward (g : SL(2,ℤ)) (tau : UpperHalfPlane) (m n : ℤ) :
    d g tau*((m:ℂ)*(g•tau:UpperHalfPlane)+(n:ℂ))=
      ((m*g 0 0+n*g 1 0:ℤ):ℂ)*tau+((m*g 0 1+n*g 1 1:ℤ):ℂ) := by
  rw [action_formula]
  push_cast
  field_simp [d_ne_zero g tau]
  simp [d]
  ring

/-- The exact inverse integer-coordinate transformation, using det(g)=1. -/
lemma period_inverse (g : SL(2,ℤ)) (tau : UpperHalfPlane) (m n : ℤ) :
    ((m:ℂ)*tau+(n:ℂ))/d g tau=
      ((g 1 1*m-g 1 0*n:ℤ):ℂ)*(g•tau:UpperHalfPlane)+((g 0 0*n-g 0 1*m:ℤ):ℂ) := by
  rw [action_formula]
  push_cast
  field_simp [d_ne_zero g tau]
  dsimp only [d]
  linear_combination -((m:ℂ)*tau+(n:ℂ))*(determinant_one g)

lemma mul_mem_lattice_iff (g : SL(2,ℤ)) (tau : UpperHalfPlane) (z : ℂ) :
    d g tau*z ∈ (periods tau).lattice ↔ z ∈ (periods (g•tau)).lattice := by
  constructor
  · intro hz
    obtain ⟨m,n,hmn⟩ := PeriodPair.mem_lattice.mp hz
    simp only [periods,mul_one] at hmn
    apply PeriodPair.mem_lattice.mpr
    refine ⟨g 1 1*m-g 1 0*n,g 0 0*n-g 0 1*m,?_⟩
    simp only [periods,mul_one]
    rw [← period_inverse,hmn]
    field_simp [d_ne_zero g tau]
  · intro hz
    obtain ⟨m,n,hmn⟩ := PeriodPair.mem_lattice.mp hz
    simp only [periods,mul_one] at hmn
    rw [← hmn,period_forward]
    apply PeriodPair.mem_lattice.mpr
    exact ⟨m*g 0 0+n*g 1 0,m*g 0 1+n*g 1 1,by simp [periods]⟩

lemma div_mem_lattice_iff (g : SL(2,ℤ)) (tau : UpperHalfPlane) (z : ℂ) :
    z/d g tau ∈ (periods (g•tau)).lattice ↔ z ∈ (periods tau).lattice := by
  have he : d g tau*(z/d g tau)=z := by field_simp [d_ne_zero g tau]
  have hh := (mul_mem_lattice_iff g tau (z/d g tau)).symm
  rwa [he] at hh

/-- Actual lattice bijection: multiply a period at g*tau by c*tau+d. -/
@[expose] def latticeEquiv (g : SL(2,ℤ)) (tau : UpperHalfPlane) :
    (periods (g•tau)).lattice ≃ (periods tau).lattice where
  toFun l := ⟨d g tau*l,(mul_mem_lattice_iff g tau l).mpr l.property⟩
  invFun l := ⟨(l:ℂ)/d g tau,(div_mem_lattice_iff g tau l).mpr l.property⟩
  left_inv l := by apply Subtype.ext; simp [d_ne_zero g tau]
  right_inv l := by apply Subtype.ext; dsimp; field_simp [d_ne_zero g tau]

lemma latticeEquiv_symm_val (g : SL(2,ℤ)) (tau : UpperHalfPlane) (l : (periods tau).lattice) :
    ((latticeEquiv g tau).symm l:ℂ)=(l:ℂ)/d g tau := rfl

end ModularLattice318
