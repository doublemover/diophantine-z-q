module
public import PELOriginalPolarizationLineBundle318
public section
noncomputable section
namespace PELOriginalSymplecticCoordinates318
open PELPrincipalOrderCoordinates318 PELOriginalPolarizationSemicharacter318
abbrev Pair:=(Fin 2→ℤ)×(Fin 2→ℤ)
/-- Exact integral basis a=(e0,e2), b=(e3,e1-2e3). No rational
rescaling or finite-index replacement of the original lattice occurs. -/
@[expose] def toPair (x:Coordinates):Pair:=(![x 0,x 2],![x 3+2*x 1,x 1])
@[expose] def fromPair (p:Pair):Coordinates:=![p.1 0,p.2 1,p.1 1,p.2 0-2*p.2 1]
lemma from_to (x:Coordinates):fromPair (toPair x)=x:=by
  ext i
  fin_cases i <;> simp [fromPair,toPair] <;> ring
lemma to_from (p:Pair):toPair (fromPair p)=p:=by
  apply Prod.ext <;> ext i <;> fin_cases i <;> simp [fromPair,toPair] <;> ring
@[expose] def coordinates:Coordinates≃ₗ[ℤ]Pair where
  toFun:=toPair
  invFun:=fromPair
  left_inv:=from_to
  right_inv:=to_from
  map_add':=by intro x y;apply Prod.ext <;> ext i <;> fin_cases i <;> simp [toPair] <;> ring
  map_smul':=by intro n x;apply Prod.ext <;> ext i <;> fin_cases i <;> simp [toPair] <;> ring
@[expose] def standard (p q:Pair):ℤ:=
  p.1 0*q.2 0+p.1 1*q.2 1-p.2 0*q.1 0-p.2 1*q.1 1
lemma exact_form (x y:Coordinates):-integralForm x y=standard (coordinates x) (coordinates y):=by
  simp [standard,coordinates,toPair,integralForm]
  ring
lemma exact_form_pair (p q:Pair):-integralForm (fromPair p) (fromPair q)=standard p q:=by
  simp [standard,fromPair,integralForm]
  ring
@[expose] def canonicalQuadratic (p:Pair):ℤ:=p.1 0*p.2 0+p.1 1*p.2 1
lemma exact_quadratic (x:Coordinates):
    canonicalQuadratic (coordinates x)-quadratic x=2*x 1*x 2:=by
  simp [canonicalQuadratic,coordinates,toPair,quadratic]
  ring
/-- The canonical theta semicharacter is EXACTLY the previously constructed
one, not a silently changed theta characteristic or line bundle. -/
lemma same_phase (x:Coordinates):
    Complex.exp ((Real.pi:ℂ)*Complex.I*(canonicalQuadratic (coordinates x):ℂ))=phase x:=by
  rw [phase]
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨x 1*x 2,?_⟩
  have h:=congrArg (fun n:ℤ=>(n:ℂ)) (exact_quadratic x)
  push_cast at h
  linear_combination (Real.pi:ℂ)*Complex.I*h
end PELOriginalSymplecticCoordinates318
