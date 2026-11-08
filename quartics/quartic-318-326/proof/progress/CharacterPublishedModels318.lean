module
public import SourceTwistArithmetic318
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public section
noncomputable section
namespace CharacterPublishedModels318
open SourceTwistArithmetic318
set_option maxHeartbeats 700000
@[expose] def shortModel (A B:ℚ):WeierstrassCurve ℚ:=⟨0,0,0,A,B⟩
@[expose] def scaleChange (u:ℚˣ):WeierstrassCurve.VariableChange ℚ:=⟨u,0,0,0⟩

theorem scale_short (u:ℚˣ) (A B:ℚ) :
    scaleChange u • shortModel ((u:ℚ)^4*A) ((u:ℚ)^6*B)=shortModel A B:=by
  have hu:(u:ℚ)≠0:=Units.ne_zero u
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp [scaleChange,shortModel,Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals ring

@[expose] def characterModel (i:Fin 4):WeierstrassCurve ℚ:=
  shortModel (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)
@[expose] def publishedModel (i:Fin 4):WeierstrassCurve ℚ:=shortModel (publishedA i) (publishedB i)
lemma scale_ne_zero (i:Fin 4) : coordinateScale i≠0:=by
  fin_cases i <;> norm_num [coordinateScale]
@[expose] def scaleUnit (i:Fin 4):ℚˣ:=Units.mk0 (coordinateScale i) (scale_ne_zero i)

/-- The four cubic character models are related to the literal published
short Weierstrass models by specified admissible rational coordinate changes. -/
theorem published_variable_change (i:Fin 4) :
    scaleChange (scaleUnit i) • characterModel i=publishedModel i:=by
  unfold characterModel publishedModel
  rw [(published_scaled_exact i).1,(published_scaled_exact i).2]
  exact scale_short (scaleUnit i) (publishedA i) (publishedB i)

/-- The inverse coordinate changes are actual inverses in the variable-change
group, so the comparison is not merely equality of j-invariants. -/
theorem character_variable_change (i:Fin 4) :
    (scaleChange (scaleUnit i))⁻¹ • publishedModel i=characterModel i:=by
  rw [←published_variable_change,inv_smul_smul]

lemma short_discriminant (A B:ℚ) :
    (shortModel A B).Δ=-16*(4*A^3+27*B^2):=by
  simp [shortModel,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem published_elliptic (i:Fin 4) : (publishedModel i).IsElliptic:=by
  constructor
  apply IsUnit.mk0
  rw [publishedModel,short_discriminant]
  exact mul_ne_zero (by norm_num) (published_nonsingular i)

theorem character_elliptic (i:Fin 4) : (characterModel i).IsElliptic:=by
  letI:=published_elliptic i
  rw [←character_variable_change]
  infer_instance
end CharacterPublishedModels318
