module
public import PELOriginalPolarizationSemicharacter318
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public section
noncomputable section
namespace PELOriginalPolarizationAutomorphy318
open QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318 PELPeriodRiemannForm318
open PELOriginalHermitianForm318 PELOriginalPolarizationSemicharacter318
variable (τ:ℂ) (hτ:0<τ.im)
abbrev L:=PELOriginalPeriodLattice318.lattice τ hτ
local notation "H" => form τ hτ
local notation "E" => riemann τ hτ

/-- Literal logarithm of the factor on the same full original lattice.
Both the quadratic correction and H use the fixed original polarization. -/
@[expose] def exponent (l:L τ hτ) (z:ComplexVectors):ℂ:=
  (Real.pi:ℂ)*(H z l.val+H l.val l.val/2)+
    (Real.pi:ℂ)*Complex.I*(quadratic ((latticeEquiv τ hτ).symm l):ℂ)
@[expose] def factor (l:L τ hτ) (z:ComplexVectors):ℂ:=Complex.exp (exponent τ hτ l z)
lemma nonzero (l:L τ hτ) (z:ComplexVectors):factor τ hτ l z≠0:=Complex.exp_ne_zero _
lemma zero_factor (z:ComplexVectors):factor τ hτ 0 z=1:=by
  simp [factor,exponent,form,zero_left,zero_right,quadratic]

/-- The exact obstruction to exponent additivity is an integral multiple
of 2πi; the half-integral-order cross terms are retained explicitly. -/
lemma exponent_cocycle (l m:L τ hτ) (z:ComplexVectors):
    exponent τ hτ l (z+m.val)+exponent τ hτ m z-exponent τ hτ (l+m) z=
      (-correction ((latticeEquiv τ hτ).symm l) ((latticeEquiv τ hτ).symm m):ℂ)*
        (2*(Real.pi:ℂ)*Complex.I):=by
  have hE:((integralRiemann τ hτ l m:ℤ):ℂ)=(E l.val m.val:ℂ):=by
    simpa using congrArg (fun r:ℝ=>(r:ℂ)) (integralRiemann_value τ hτ l m).symm
  have hQ:=congrArg (fun n:ℤ=>(n:ℂ))
    (quadratic_add ((latticeEquiv τ hτ).symm l) ((latticeEquiv τ hτ).symm m))
  change _=((-integralForm _ _+2*correction _ _:ℤ):ℂ) at hQ
  push_cast at hQ
  have hS:=skew_difference τ hτ l.val m.val
  simp only [exponent,Submodule.coe_add,map_add,form_add_left,form_add_right]
  change ((-integralForm _ _:ℤ):ℂ)=(E l.val m.val:ℂ) at hE
  push_cast at hE
  linear_combination (Real.pi:ℂ)/2*hS-(Real.pi:ℂ)*Complex.I*hQ-
    (Real.pi:ℂ)*Complex.I*hE

/-- Genuine automorphy on the ACTUAL lattice action z↦z+l. -/
lemma cocycle (l m:L τ hτ) (z:ComplexVectors):
    factor τ hτ (l+m) z=factor τ hτ l (z+m.val)*factor τ hτ m z:=by
  symm
  rw [factor,factor,←Complex.exp_add,factor]
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  exact ⟨-correction ((latticeEquiv τ hτ).symm l) ((latticeEquiv τ hτ).symm m),
    by simpa only [Int.cast_neg] using exponent_cocycle τ hτ l m z⟩

/-- Affine-exponential factors are entire in the ORIGINAL C² period
coordinate. No algebraic line bundle or canonical rational model is asserted. -/
lemma holomorphic (l:L τ hτ):ContDiff ℂ ⊤ (factor τ hτ l):=by
  have h:ContDiff ℂ ⊤ (fun z:ComplexVectors=>H z l.val):=
    (continuousLinear τ hτ l.val).contDiff
  exact (Complex.contDiff_exp.comp
    (((h.add contDiff_const).const_mul (Real.pi:ℂ)).add contDiff_const))

@[expose] def action (l:L τ hτ) (p:ComplexVectors×ℂ):ComplexVectors×ℂ:=
  (p.1+l.val,factor τ hτ l p.1*p.2)
lemma action_zero (p:ComplexVectors×ℂ):action τ hτ 0 p=p:=by
  simp [action,zero_factor]
lemma action_add (l m:L τ hτ) (p:ComplexVectors×ℂ):
    action τ hτ (l+m) p=action τ hτ l (action τ hτ m p):=by
  ext
  · simp [action,add_comm,add_left_comm,add_assoc]
  · simp only [action,cocycle,mul_assoc]
lemma action_preserves_zero (l:L τ hτ) (z:ComplexVectors):
    action τ hτ l (z,0)=(z+l.val,0):=by simp [action]
lemma fiber_linear (l:L τ hτ) (z:ComplexVectors) (a b c:ℂ):
    (action τ hτ l (z,a*b+c)).2=
      a*(action τ hτ l (z,b)).2+(action τ hτ l (z,c)).2:=by
  simp only [action]
  ring
end PELOriginalPolarizationAutomorphy318
