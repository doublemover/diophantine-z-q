module
public import OriginalSameJSymplecticPeriods318
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Complex.Module

@[expose] public section
noncomputable section

namespace OriginalSameJGroupedPeriodBasis318

open Matrix OriginalSameJSymplecticPeriods318 OriginalSameJRealificationDet318

variable (g : ℕ)

/-- One fixed ordered real coordinate system for the actual complex
cotangent frame: all real rows followed by all imaginary rows. -/
abbrev Index := Fin g ⊕ Fin g
abbrev V := Fin g→ℂ

def groupedCoordinates : V g ≃ₗ[ℝ] (Index g→ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun x i := (x (.inl i) : ℂ) + (x (.inr i) : ℂ)*Complex.I
  left_inv z := by
    funext i
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
  right_inv x := by
    funext i
    cases i <;> simp [Complex.mul_re,Complex.mul_im]
  map_add' x y := by
    funext i
    cases i <;> rfl
  map_smul' r x := by
    funext i
    cases i <;> simp [Complex.real_smul,Complex.mul_re,Complex.mul_im]

def referenceBasis : Module.Basis (Index g) ℝ (V g) :=
  Module.Basis.ofEquivFun (groupedCoordinates g)

variable {g}
variable (P Q : Mat ℂ (Fin g))

/-- These are literal columns of the two matrices of cycle periods in the
unchanged order, not an independent spanning family of the Lie algebra. -/
def periodColumn : Index g → V g :=
  Sum.elim (fun j i => P i j) (fun j i => Q i j)

theorem grouped_read (r j : Index g) :
    groupedCoordinates g (periodColumn P Q j) r = groupedReal P Q r j := by
  cases r <;> cases j <;> rfl

variable (G : Mat ℂ (Fin g))
variable (h : complexIsotropy P Q=0)
variable (hG : mixedPairing P Q = ((2:ℂ)*Complex.I) • G) (hp : 0<G.det.re)

include G h hG hp in
theorem matrix_nonsingular : (groupedReal P Q).det ≠ 0 := by
  intro he
  have hg := actual_determinant P Q G h hG hp
  rw [he,abs_zero] at hg
  exact (ne_of_gt hp) hg.symm

/-- The exact point-level J periods are a REAL basis before any assertion
about equality to the integer kernel. Consequently the Haar route cannot
hide a merely real-span frame in lieu of the actual period columns. -/
def periodBasis : Module.Basis (Index g) ℝ (V g) :=
  (referenceBasis g).map ((groupedReal P Q).toLinearEquiv (referenceBasis g)
    (isUnit_iff_ne_zero.mpr (matrix_nonsingular P Q G h hG hp)))

theorem reads_basis (j : Index g) : periodBasis P Q G h hG hp j = periodColumn P Q j := by
  apply (groupedCoordinates g).injective
  funext r
  calc
    groupedCoordinates g (periodBasis P Q G h hG hp j) r =
        (referenceBasis g).repr (periodBasis P Q G h hG hp j) r :=
      (Module.Basis.ofEquivFun_repr_apply (groupedCoordinates g) (periodBasis P Q G h hG hp j) r).symm
    _ = groupedReal P Q r j := by
      rw [periodBasis,Module.Basis.map_apply,Matrix.toLinearEquiv_apply,Matrix.toLin_self,
        Module.Basis.repr_sum_self]
    _ = groupedCoordinates g (periodColumn P Q j) r := (grouped_read P Q r j).symm

include G h hG hp in
theorem actual_real_span : Submodule.span ℝ (Set.range (periodColumn P Q)) = ⊤ := by
  have he : (periodBasis P Q G h hG hp : Index g→V g) = periodColumn P Q :=
    funext (reads_basis P Q G h hG hp)
  rw [←he]
  exact (periodBasis P Q G h hG hp).span_eq

end OriginalSameJGroupedPeriodBasis318

#print axioms OriginalSameJGroupedPeriodBasis318.grouped_read
#print axioms OriginalSameJGroupedPeriodBasis318.reads_basis
#print axioms OriginalSameJGroupedPeriodBasis318.actual_real_span
