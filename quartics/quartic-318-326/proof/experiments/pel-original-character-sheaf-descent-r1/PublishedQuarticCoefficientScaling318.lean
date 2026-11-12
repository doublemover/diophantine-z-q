module
public import PublishedEllipticModels318
public import ShortScaling318
public section
noncomputable section
namespace PublishedQuarticCoefficientScaling318

/-- Literal five quartic coefficients in the SAME original character
order105,70,42,30. No curve is identified from its name or numeric label. -/
@[expose] def row : Fin 4→Fin 5→ℚ:=
  ![![-43,2,505,12,-1548],![-43,256,-130,-768,-387],
    ![-43,600,-986,-600,-43],![-43,-686,-2915,-1372,-172]]
@[expose] def I (i:Fin 4):ℚ:=12*row i 0*row i 4-3*row i 1*row i 3+(row i 2)^2
@[expose] def J (i:Fin 4):ℚ:=72*row i 0*row i 2*row i 4+
  9*row i 1*row i 2*row i 3-27*row i 0*(row i 3)^2-
  27*(row i 1)^2*row i 4-2*(row i 2)^3
@[expose] def factor : Fin 4→ℚ:=![1,1/2,1/2,1]
lemma factor_ne (i:Fin 4) : (factor i:ℂ)≠0:=by
  fin_cases i <;> norm_num [factor]
@[expose] def unit (i:Fin 4):ℂˣ:=Units.mk0 (factor i:ℂ) (factor_ne i)

/-- Concrete invariant cubic of the quartic coefficient tuple. Calling
this its Jacobian still requires the actual quartic/model comparison;
this file proves the exact equations and coordinate scaling only. -/
@[expose] def invariantCurve (i:Fin 4):WeierstrassCurve ℂ:=
  NormalizedWeierstrass318.model (16*(I i:ℂ)) (32*(J i:ℂ))
instance short (i:Fin 4) : (invariantCurve i).IsShortNF:=⟨rfl,rfl,rfl⟩
lemma coefficients (i:Fin 4) :
    (invariantCurve i).a₄= -(I i:ℂ)/3 ∧ (invariantCurve i).a₆= -(J i:ℂ)/27:=by
  constructor
  · change -(16*(I i:ℂ))/48= -(I i:ℂ)/3
    ring
  · change -(32*(J i:ℂ))/864= -(J i:ℂ)/27
    ring
lemma exact_scaling (i:Fin 4) :
    (PublishedEllipticModels318.curve i).a₄=(unit i:ℂ)^4*(invariantCurve i).a₄ ∧
    (PublishedEllipticModels318.curve i).a₆=(unit i:ℂ)^6*(invariantCurve i).a₆ := by
  rw [(PublishedEllipticModels318.coefficients i).1,
    (PublishedEllipticModels318.coefficients i).2,(coefficients i).1,(coefficients i).2]
  fin_cases i <;> norm_num [unit,factor,I,J,row,PublishedEllipticModels318.A,PublishedEllipticModels318.B]

lemma discriminant_ne (i:Fin 4) : (invariantCurve i).Δ≠0:=by
  rw [invariantCurve,NormalizedWeierstrass318.model_discriminant]
  fin_cases i <;> norm_num [I,J,row]
instance elliptic (i:Fin 4) : (invariantCurve i).IsElliptic:=
  ⟨isUnit_iff_ne_zero.mpr (discriminant_ne i)⟩

theorem native_j_quartic (i:Fin 4) : (invariantCurve i).j=
    (ContactCoordinates318.quarticJ (row i 0) (row i 1) (row i 2) (row i 3) (row i 4):ℂ) := by
  rw [invariantCurve,NormalizedWeierstrass318.model_j]
  fin_cases i <;> norm_num [I,J,row,ContactCoordinates318.quarticJ]

theorem table_j_quartic (i:Fin 4) : (PublishedEllipticModels318.curve i).j=
    (ContactCoordinates318.quarticJ (row i 0) (row i 1) (row i 2) (row i 3) (row i 4):ℂ) := by
  rw [PublishedEllipticModels318.native_j]
  fin_cases i <;> norm_num [PublishedEllipticModels318.jValue,row,ContactCoordinates318.quarticJ]

/-- An actual group isomorphism of the TWO specified elliptic models,
with literal finite coordinates and the actual point at infinity.
This is NOT an identification of either model with the original PEL curve. -/
@[expose] def pointAddEquiv (i:Fin 4) :
    (invariantCurve i).toAffine.Point ≃+ (PublishedEllipticModels318.curve i).toAffine.Point :=
  ShortScaling318.pointAddEquiv _ _ (unit i) (exact_scaling i).1 (exact_scaling i).2
lemma infinity (i:Fin 4) : pointAddEquiv i 0=0:=(pointAddEquiv i).map_zero

lemma finite_equation (i:Fin 4) (x y:ℂ) :
    (PublishedEllipticModels318.curve i).toAffine.Equation ((unit i:ℂ)^2*x) ((unit i:ℂ)^3*y) ↔
      (invariantCurve i).toAffine.Equation x y :=
  ShortScaling318.equation_scale _ _ (unit i) (exact_scaling i).1 (exact_scaling i).2 x y
end PublishedQuarticCoefficientScaling318
