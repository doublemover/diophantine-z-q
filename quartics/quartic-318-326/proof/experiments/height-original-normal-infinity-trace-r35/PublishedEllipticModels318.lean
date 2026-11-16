module
public import NormalizedWeierstrass318
public import ContactCoordinates318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public section
noncomputable section
namespace PublishedEllipticModels318

/-- Literal Table3 short coefficients in ORIGINAL coordinate-character
order105,70,42,30. These define concrete curves; the identification with
our original analytic PEL quotients is NOT assumed or asserted here. -/
@[expose] def labels : Fin 4→ℕ:=![105,70,42,30]
@[expose] def A : Fin 4→ℚ:=![-1053721/3,-50401/3,-129649/3,-5762401/3]
@[expose] def B : Fin 4→ℚ:=![-2163135238/27,-22628702/27,-90882286/27,-27665272798/27]
@[expose] def delta : Fin 4→ℚ:=![444110104166400,40642560000,271063296000000,531284060160000]
@[expose] def jValue : Fin 4→ℚ:=![1169975873419524361/108425318400,
  128031684631201/9922500,2179252305146449/66177562500,191342053882402567201/129708022500]
@[expose] def curve (i:Fin 4) : WeierstrassCurve ℂ:=
  NormalizedWeierstrass318.model (-48*(A i:ℂ)) (-864*(B i:ℂ))

lemma coefficients (i:Fin 4) : (curve i).a₄=(A i:ℂ) ∧ (curve i).a₆=(B i:ℂ):=by
  constructor
  · change -(-48*(A i:ℂ))/48=(A i:ℂ)
    ring
  · change -(-864*(B i:ℂ))/864=(B i:ℂ)
    ring
instance short (i:Fin 4) : (curve i).IsShortNF:=⟨rfl,rfl,rfl⟩

lemma discriminant (i:Fin 4) : (curve i).Δ=(delta i:ℂ):=by
  rw [curve,NormalizedWeierstrass318.model_discriminant]
  fin_cases i <;> norm_num [A,B,delta]
lemma delta_ne (i:Fin 4) : (delta i:ℂ)≠0:=by
  fin_cases i <;> norm_num [delta]
instance elliptic (i:Fin 4) : (curve i).IsElliptic:=by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [discriminant]
  exact delta_ne i

/-- Native Mathlib j of the actual nonsingular Table3 Weierstrass curve,
not a fresh uninterpreted assignment of a number to a PEL quotient. -/
theorem native_j (i:Fin 4) : (curve i).j=(jValue i:ℂ):=by
  rw [curve,NormalizedWeierstrass318.model_j]
  fin_cases i <;> norm_num [A,B,jValue]

lemma equation (i:Fin 4) (x y:ℂ) : (curve i).toAffine.Equation x y ↔
    y^2=x^3+(A i:ℂ)*x+(B i:ℂ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change y^2+0*x*y+0*y=x^3+0*x^2+(-(-48*(A i:ℂ))/48)*x+
    (-(-864*(B i:ℂ))/864) ↔ _
  have h4:-(-48*(A i:ℂ))/48=(A i:ℂ):=by ring
  have h6:-(-864*(B i:ℂ))/864=(B i:ℂ):=by ring
  rw [h4,h6]
  simp
end PublishedEllipticModels318
