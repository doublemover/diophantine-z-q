module
public import ActualTwoDescentFieldSquareOneMaps318
public section
noncomputable section
namespace ActualTwoDescentFieldScalarSquareRoots318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldSquareOneUnits318

lemma actual_scalar_root_exists (a : Fˣ) : ∃ r : Qbar, r ≠ 0 ∧ r^2=algebraMap F Qbar (a : F) := by
  obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Qbar (a : F)) (by decide : 0 < (2 : ℕ))
  refine ⟨r,?_,hr⟩
  intro he
  rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hr
  exact rational_parameter_ne (a : F) a.ne_zero hr.symm

def scalarRoot (a : Fˣ) : Qbar := Classical.choose (actual_scalar_root_exists a)
lemma scalar_root_ne (a : Fˣ) : scalarRoot a ≠ 0 := (Classical.choose_spec (actual_scalar_root_exists a)).1
lemma scalar_root_square (a : Fˣ) : (scalarRoot a)^2=algebraMap F Qbar (a : F) := (Classical.choose_spec (actual_scalar_root_exists a)).2

lemma actual_root_ratio_square (a : Fˣ) (r : Qbar) (hr : r ≠ 0)
    (hs : r^2=algebraMap F Qbar (a : F)) (σ : GalQ) : (σ r/r)^2=1 := by
  rw [div_pow,←map_pow,hs,σ.commutes,div_self (rational_parameter_ne _ a.ne_zero)]

def rootRatio (a : Fˣ) (r : Qbar) (hr : r ≠ 0) (hs : r^2=algebraMap F Qbar (a : F)) (σ : GalQ) : SquareOne Qbar :=
  ⟨Units.mk0 (σ r/r) (div_ne_zero (ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero σ.toRingHom hr) hr),by
    apply Units.ext
    exact actual_root_ratio_square a r hr hs σ⟩

end ActualTwoDescentFieldScalarSquareRoots318
