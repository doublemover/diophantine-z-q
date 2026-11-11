module
public import PELOriginalHermitianForm318
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public section
noncomputable section
namespace PELOriginalPolarizationSemicharacter318
open PELPrincipalOrderCoordinates318 PELPeriodRiemannForm318
variable (τ:ℂ) (hτ:0<τ.im)
/-- Quadratic refinement of the ACTUAL positive integral form. The term
2x0x1 comes from the specified half-integral quaternion order basis. -/
@[expose] def quadratic (x:Coordinates):ℤ:=2*x 0*x 1+x 0*x 3-x 1*x 2
@[expose] def correction (x y:Coordinates):ℤ:=2*x 1*y 0+x 3*y 0-x 2*y 1
lemma quadratic_add (x y:Coordinates):
    quadratic (x+y)-quadratic x-quadratic y=
      -integralForm x y+2*correction x y:=by
  simp only [quadratic,correction,integralForm,Pi.add_apply]
  ring
lemma quadratic_neg (x:Coordinates):quadratic (-x)=quadratic x:=by
  simp only [quadratic,Pi.neg_apply]
  ring
@[expose] def phase (x:Coordinates):ℂ:=
  Complex.exp ((Real.pi:ℂ)*Complex.I*(quadratic x:ℂ))
lemma phase_nonzero (x:Coordinates):phase x≠0:=Complex.exp_ne_zero _
lemma phase_zero:phase 0=1:=by simp [phase,quadratic]
lemma phase_neg (x:Coordinates):phase (-x)=phase x:=by rw [phase,quadratic_neg];rfl
lemma phase_square (x:Coordinates):phase x*phase x=1:=by
  rw [phase,←Complex.exp_add]
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨quadratic x,?_⟩
  ring
/-- The sign law is derived at the exact integral order, not imposed as
an additional semicharacter hypothesis on the period lattice. -/
lemma phase_add (x y:Coordinates):
    phase (x+y)=phase x*phase y*
      Complex.exp ((Real.pi:ℂ)*Complex.I*((-integralForm x y:ℤ):ℂ)):=by
  simp only [phase,←Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨correction x y,?_⟩
  have h:=congrArg (fun n:ℤ=>(n:ℂ)) (quadratic_add x y)
  push_cast at h
  linear_combination (Real.pi:ℂ)*Complex.I*h

@[expose] def latticePhase (x:PELOriginalPeriodLattice318.lattice τ hτ):ℂ:=
  phase ((latticeEquiv τ hτ).symm x)
lemma latticePhase_add (x y:PELOriginalPeriodLattice318.lattice τ hτ):
    latticePhase τ hτ (x+y)=latticePhase τ hτ x*latticePhase τ hτ y*
      Complex.exp ((Real.pi:ℂ)*Complex.I*(integralRiemann τ hτ x y:ℂ)):=by
  simp only [latticePhase,map_add]
  exact phase_add _ _
end PELOriginalPolarizationSemicharacter318
