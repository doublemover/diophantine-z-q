module
public import ProductLocalization318
public import InvariantChartForms318
public import WeierstrassKaehler318
public section
noncomputable section
namespace FiniteInvariantDifferential318
open KaehlerDifferential ShortAffineJacobian318 ProductLocalization318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- The actual derivative relation in the literal affine coordinate algebra. -/
theorem differentiated_relation (A B : R) :
    (presentation A B 0).jacobian • D R (Ring A B) (x A B)=
      -(presentation A B 1).jacobian • D R (Ring A B) (y A B) := by
  have h:=congrArg (D R (Ring A B)) (relation A B)
  simp only [map_sub,Derivation.leibniz_pow,Derivation.leibniz,
    Derivation.map_algebraMap,smul_zero,add_zero,map_zero] at h
  norm_num at h
  rw [jacobian_x,jacobian_y]
  linear_combination (norm := module) h

abbrev XChart (A B : R) := WeierstrassKaehler318.AffineChart A B 0
abbrev YChart (A B : R) := WeierstrassKaehler318.AffineChart A B 1
abbrev CommonRing (A B : R) := Common (presentation A B 0).jacobian (presentation A B 1).jacobian

/-- The actual dy form on the chart where the x-Jacobian minor is invertible. -/
@[expose] def xForm (A B : R) : KaehlerDifferential R (XChart A B) :=
  -IsLocalization.Away.invSelf (S:=XChart A B) (presentation A B 0).jacobian •
    D R (XChart A B) (algebraMap (Ring A B) (XChart A B) (y A B))
/-- The previously constructed actual dx/(2y) form. -/
abbrev yForm (A B : R) := InvariantChartForms318.finite A B

@[expose] def xMap (A B : R) : XChart A B →ₐ[R] CommonRing A B :=
  leftMap (presentation A B 0).jacobian (presentation A B 1).jacobian
@[expose] def yMap (A B : R) : YChart A B →ₐ[R] CommonRing A B :=
  rightMap (presentation A B 0).jacobian (presentation A B 1).jacobian

@[expose] def commonX (A B : R) : KaehlerDifferential R (CommonRing A B) :=
  -inverseLeft (presentation A B 0).jacobian (presentation A B 1).jacobian •
    D R (CommonRing A B) (algebraMap (Ring A B) (CommonRing A B) (y A B))
@[expose] def commonY (A B : R) : KaehlerDifferential R (CommonRing A B) :=
  inverseRight (presentation A B 0).jacobian (presentation A B 1).jacobian •
    D R (CommonRing A B) (algebraMap (Ring A B) (CommonRing A B) (x A B))

theorem x_pullback (A B : R) : AlgHomDifferential318.map (xMap A B) (xForm A B)=commonX A B := by
  rw [xForm,AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,map_neg]
  simp only [xMap,leftMap_inverse,leftMap_integral,commonX]

theorem y_pullback (A B : R) : AlgHomDifferential318.map (yMap A B) (yForm A B)=commonY A B := by
  rw [yForm,InvariantChartForms318.finite,AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D]
  simp only [yMap,rightMap_inverse,rightMap_integral,commonY]

theorem common_forms_equal (A B : R) : commonY A B=commonX A B := by
  let j0 := (presentation A B 0).jacobian
  let j1 := (presentation A B 1).jacobian
  let φ:=algebraMap (Ring A B) (CommonRing A B)
  have h:=congrArg (KaehlerDifferential.map R R (Ring A B) (CommonRing A B))
    (differentiated_relation A B)
  simp only [map_smul,KaehlerDifferential.map_D] at h
  rw [←IsScalarTower.algebraMap_smul (CommonRing A B) j0,
    ←IsScalarTower.algebraMap_smul (CommonRing A B) (-j1),map_neg] at h
  have he:=congrArg (fun ω : KaehlerDifferential R (CommonRing A B) =>
    (inverseLeft j0 j1 * inverseRight j0 j1) • ω) h
  have h0 : (inverseLeft j0 j1 * inverseRight j0 j1)*φ j0=inverseRight j0 j1 := by
    calc _=inverseRight j0 j1*(φ j0*inverseLeft j0 j1) := by ring
         _=_ := by rw [left_inverse,mul_one]
  have h1 : (inverseLeft j0 j1 * inverseRight j0 j1)*(-φ j1)= -inverseLeft j0 j1 := by
    calc _= -inverseLeft j0 j1*(φ j1*inverseRight j0 j1) := by ring
         _=_ := by rw [right_inverse,mul_one]
  simp only [smul_smul] at he
  change ((inverseLeft j0 j1 * inverseRight j0 j1)*φ j0) • _ =
    ((inverseLeft j0 j1 * inverseRight j0 j1)*(-φ j1)) • _ at he
  rw [h0,h1] at he
  exact he

/-- Genuine relative invariant-form compatibility between both actual finite Jacobian charts. -/
theorem invariant_overlap (A B : R) :
    AlgHomDifferential318.map (yMap A B) (yForm A B)=
      AlgHomDifferential318.map (xMap A B) (xForm A B) := by
  rw [x_pullback,y_pullback,common_forms_equal]

theorem x_frame_value (A B : R) :
    WeierstrassKaehler318.affineFrame A B 0 (xForm A B)=
      -IsLocalization.Away.invSelf (S:=XChart A B) (presentation A B 0).jacobian := by
  rw [xForm,map_smul,WeierstrassKaehler318.affineFrame_dy,smul_eq_mul,mul_one]

theorem xForm_generates (A B : R) : Submodule.span (XChart A B) (Set.singleton (xForm A B))=⊤ := by
  apply top_le_iff.mp
  intro ω _
  apply Submodule.mem_span_singleton.mpr
  refine ⟨-WeierstrassKaehler318.affineFrame A B 0 ω *
    algebraMap (Ring A B) (XChart A B) (presentation A B 0).jacobian,?_⟩
  apply (WeierstrassKaehler318.affineFrame A B 0).injective
  rw [map_smul,x_frame_value,smul_eq_mul,neg_mul,neg_mul_neg,mul_assoc,
    IsLocalization.Away.mul_invSelf,mul_one]
end FiniteInvariantDifferential318
