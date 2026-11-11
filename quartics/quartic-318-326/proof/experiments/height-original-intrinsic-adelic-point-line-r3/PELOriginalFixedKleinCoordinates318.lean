module
public import PELDirichletHeight318
public import QuaternionicFixedParameter318
public section
noncomputable section
namespace PELOriginalFixedKleinCoordinates318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELQuaternionRealRepresentation318 PELDirichletHeight318
open QuaternionicFixedParameter318
set_option maxHeartbeats 2400000

/-- Literal real representation of the original trace-zero order element,
with r = 2*x₁+x₃, a = x₀, d = x₃. This is not a new action or chart. -/
@[expose] def traceZeroMatrix (a r d : ℝ) : RealMatrices :=
  !![-beta*a, -alpha*r/2+alpha*beta*d/10;
      alpha*r/2+alpha*beta*d/10, beta*a]

/-- The two actual Klein coordinates of a fixed point are forced by the
original matrix entries. No candidate fixed point or fundamental-domain
hypothesis is supplied. The equations remain valid before dividing by r. -/
theorem fixed_coordinates_mul (a r d : ℝ) (τ : HalfPlane)
    (hfix : fixesLine (traceZeroMatrix a r d) τ) :
    scaledFirst τ*r = -10*a ∧ scaledSecond τ*r = -d := by
  obtain ⟨ha,hb⟩ := coordinate_relations (traceZeroMatrix a r d) τ τ.property hfix
  let x := (τ:ℂ).re
  let s := Complex.normSq (τ:ℂ)
  let c := alpha*r/2+alpha*beta*d/10
  have hn : s+1≠0 := by dsimp [s]; nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  have hcx : c*x = -beta*a := by
    change -beta*a=beta*a+2*c*x at ha
    linarith
  have hbs : -alpha*r/2+alpha*beta*d/10 = -c*s := by
    simpa only [traceZeroMatrix,Matrix.cons_val_zero,Matrix.cons_val_one,
      Complex.normSq_apply,pow_two] using hb
  have hsum : c*(s+1)=alpha*r := by dsimp [c] at *; nlinarith only [hbs]
  have hdiff : c*(s-1)= -alpha*beta*d/5 := by dsimp [c] at *; nlinarith only [hbs]
  constructor
  · change alpha*beta*(2*x/(s+1))*r = -10*a
    field_simp [hn]
    linear_combination -(2*beta*x)*hsum + (2*beta*(s+1))*hcx -
      (2*a*(s+1))*beta_sq
  · change beta*((s-1)/(s+1))*r = -d
    have he : alpha*(beta*(s-1)*r+d*(s+1))=0 := by
      linear_combination -(beta*(s-1))*hsum + (beta*(s+1))*hdiff -
        (alpha*d*(s+1)/5)*beta_sq
    have he' := (mul_eq_zero.mp he).resolve_left alpha_pos.ne'
    field_simp [hn]
    linarith

theorem fixed_coordinates (a r d : ℝ) (τ : HalfPlane)
    (hr : r≠0) (hfix : fixesLine (traceZeroMatrix a r d) τ) :
    scaledFirst τ = -10*a/r ∧ scaledSecond τ = -d/r := by
  obtain ⟨h₁,h₂⟩ := fixed_coordinates_mul a r d τ hfix
  exact ⟨(eq_div_iff hr).mpr h₁,(eq_div_iff hr).mpr h₂⟩

/-- Exact original fixed-point height, squared to avoid introducing any
chosen square root. Together with the proved polygon height bound this
bounds the actual integral coordinate r, not an abstract model point. -/
theorem fixed_height_square (a r d m : ℝ) (τ : HalfPlane)
    (hm : 105*r^2-10*a^2-21*d^2=2*m) (hr : r≠0)
    (hfix : fixesLine (traceZeroMatrix a r d) τ) :
    m*(height τ)^2=210*r^2 := by
  obtain ⟨hf,hs⟩ := fixed_coordinates a r d τ hr hfix
  have hid := disk_height_identity τ
  rw [hf,hs] at hid
  field_simp [hr] at hid
  nlinarith only [hid,congrArg (fun t : ℝ => t*(height τ)^2) hm]

/-- A finite bound with all constants retained from the original polygon. -/
theorem bounded_original_coordinate (a r d m : ℝ) (τ : HalfPlane)
    (hm : 105*r^2-10*a^2-21*d^2=2*m) (hmpos : 0<m)
    (hfix : fixesLine (traceZeroMatrix a r d) τ) (hheight : height τ≤200) :
    210*r^2≤40000*m := by
  have hr : r≠0 := by intro h; rw [h] at hm; nlinarith [sq_nonneg a,sq_nonneg d]
  have he := fixed_height_square a r d m τ hm hr hfix
  have hs : (height τ)^2≤40000 := by nlinarith [height_pos τ]
  nlinarith [mul_le_mul_of_nonneg_left hs hmpos.le]
end PELOriginalFixedKleinCoordinates318
