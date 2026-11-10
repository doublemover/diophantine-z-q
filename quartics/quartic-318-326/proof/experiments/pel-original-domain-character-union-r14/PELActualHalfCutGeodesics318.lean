module
public import PELMaximalActualJordanDomain318
public import GeodesicCircleFlattening318
public section
noncomputable section
namespace PELActualHalfCutGeodesics318
open Complex Set
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELQuaternionRealRepresentation318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
set_option maxHeartbeats 2400000

/-- The four original right/bottom/top circle equations; left circles are
obtained by the already proved genuine anti-holomorphic mirror. -/
@[expose] def leading : Fin 4 → ℝ := ![1,beta-1,30,35-7*beta]
@[expose] def middle : Fin 4 → ℝ := ![0,0,alpha*beta,alpha*beta]
@[expose] def circleConstant : Fin 4 → ℝ := ![-1,-beta-1,30,35+7*beta]
@[expose] def discriminant : Fin 4 → ℝ := ![1,4,150,70]
@[expose] def equation (i : Fin 4) (z : ℂ) : ℝ :=
  leading i*Complex.normSq z-2*middle i*z.re+circleConstant i

theorem leading_pos (i : Fin 4) : 0<leading i := by
  have hβ : 1<beta := by nlinarith [beta_pos,beta_sq]
  have hβ' : beta<5 := by nlinarith [beta_pos,beta_sq]
  fin_cases i <;> norm_num [leading] <;> linarith

theorem discriminant_pos (i : Fin 4) : 0<discriminant i := by
  fin_cases i <;> norm_num [discriminant]

theorem discriminant_identity (i : Fin 4) :
    (middle i)^2-leading i*circleConstant i=discriminant i := by
  have hab : (alpha*beta)^2=1050 := by rw [mul_pow,alpha_sq,beta_sq]; norm_num
  fin_cases i <;> norm_num [middle,leading,circleConstant,discriminant] <;> nlinarith [beta_sq]

@[expose] def leftEndpoint (i : Fin 4) : ℝ :=
  (middle i-Real.sqrt (discriminant i))/leading i
@[expose] def rightEndpoint (i : Fin 4) : ℝ :=
  (middle i+Real.sqrt (discriminant i))/leading i

theorem endpoints_ordered (i : Fin 4) : leftEndpoint i<rightEndpoint i := by
  unfold leftEndpoint rightEndpoint
  exact (div_lt_div_iff_of_pos_right (leading_pos i)).mpr
    (by linarith [Real.sqrt_pos.mpr (discriminant_pos i)])

theorem endpoint_sum (i : Fin 4) :
    leftEndpoint i+rightEndpoint i=2*middle i/leading i := by
  unfold leftEndpoint rightEndpoint
  ring

theorem endpoint_product (i : Fin 4) :
    leftEndpoint i*rightEndpoint i=circleConstant i/leading i := by
  have hs := Real.sq_sqrt (discriminant_pos i).le
  have hd := discriminant_identity i
  unfold leftEndpoint rightEndpoint
  field_simp [(leading_pos i).ne']
  nlinarith

/-- Every edge's circle has two distinct real endpoints and an explicit
holomorphic flattening with no pole in the original half-plane. -/
theorem flatten_equation (i : Fin 4) (τ : HalfPlane) :
    (GeodesicCircleFlattening318.flatten (leftEndpoint i) (rightEndpoint i) τ).im=0 ↔
      equation i τ=0 := by
  rw [GeodesicCircleFlattening318.flatten_real_iff_circle _ _ _ τ.property,
    endpoint_sum,endpoint_product]
  have h := (leading_pos i).ne'
  constructor <;> intro he
  · unfold equation
    field_simp [h] at he
    nlinarith
  · unfold equation at he
    field_simp [h]
    nlinarith

theorem flatten_positive (i : Fin 4) (τ : HalfPlane) :
    0<(GeodesicCircleFlattening318.flatten (leftEndpoint i) (rightEndpoint i) τ).re :=
  GeodesicCircleFlattening318.flatten_re_pos _ _ (endpoints_ordered i) _ τ.property

/-- Exact equations of the ORIGINAL scaled-coordinate edges in the
actual complex half-plane. These are genuine semicircles, not the straight
Klein edges mistaken for complex coordinate lines. -/
theorem actual_edge_equations (τ : HalfPlane) :
    (scaledSecond τ=0 ↔ equation 0 τ=0) ∧
    (scaledSecond τ=1 ↔ equation 1 τ=0) ∧
    (scaledFirst τ=30 ↔ equation 2 τ=0) ∧
    (scaledFirst τ+7*scaledSecond τ=35 ↔ equation 3 τ=0) := by
  have hn : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  have hb := beta_pos.ne'
  unfold scaledFirst scaledSecond firstDisk secondDisk
  norm_num [equation,leading,middle,circleConstant]
  constructor
  · constructor <;> intro h
    · field_simp [hn] at h
      exact (mul_eq_zero.mp h).resolve_left hb
    · rw [sub_eq_zero.mp h]
      ring
  constructor
  · constructor <;> intro h <;> field_simp [hn] at * <;> nlinarith
  constructor
  · constructor <;> intro h <;> field_simp [hn] at * <;> nlinarith
  · constructor <;> intro h <;> field_simp [hn] at * <;> nlinarith
end PELActualHalfCutGeodesics318
