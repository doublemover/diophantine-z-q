module
public import PELStrictPolygonExtension318
public section
noncomputable section
namespace PELOriginalInteriorUniqueness318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELJointNormOneAction318
open PELDirichletOriginalUnits318 PELDirichletHeight318 PELOriginalDirichletPolygon318
open PELOriginalAllUnitMinimum318 PELStrictPolygonExtension318
open PELRealProjectiveDifferential318 PELOriginalProjectiveTangents318
set_option maxHeartbeats 1800000

/-- The actual original upper-half-plane point with scaled Klein coordinate0. -/
@[expose] def center : HalfPlane := ⟨Complex.I,by norm_num⟩

theorem center_coordinates : scaledFirst center=0 ∧ scaledSecond center=0 := by
  norm_num [scaledFirst,scaledSecond,firstDisk,secondDisk,center,Complex.normSq_apply]

theorem center_height : height center=2 := by
  norm_num [height,center,Complex.normSq_apply]

/-- Height2 characterizes the actual point i, not merely an abstract orbit. -/
theorem height_two_unique (τ : HalfPlane) (h : height τ=2) : τ=center := by
  have hy := τ.property
  have he := (div_eq_iff hy.ne').mp h
  simp only [Complex.normSq_apply] at he
  have hre : (τ:ℂ).re=0 := by
    nlinarith [sq_nonneg (τ:ℂ).re,sq_nonneg ((τ:ℂ).im-1)]
  have him : (τ:ℂ).im=1 := by
    nlinarith [sq_nonneg ((τ:ℂ).im-1)]
  apply Subtype.ext
  apply Complex.ext
  · simpa only [center,Complex.I_re] using hre
  · simpa only [center,Complex.I_im] using him

/-- If an original norm-one unit has multiplier1 at a strict polygon point,
then it belongs to the actual central sign kernel. This is not a numerical
near-equality or an appeal to a selected finite list of possible units. -/
theorem equality_implies_sign (u : normOneUnits) (A B : ℝ)
    (hP : strictInequalities A B)
    (heq : denominator (realMatrix ((u.val:order):PELQuaternionAlgebra318.B)) (A,B)=1) :
    u.val=1 ∨ u.val= -1 := by
  obtain ⟨x,hx⟩ := (show ((u.val:order):PELQuaternionAlgebra318.B)∈order from
    (u.val:order).property)
  have hn : integerNorm x=1 := by
    have h := (mem_normOneUnits u.val).mp u.property
    rw [← hx,embed_norm] at h
    exact_mod_cast h
  let M := realMatrix ((u.val:order):PELQuaternionAlgebra318.B)
  have hall (X Y : ℝ) (hXY : inequalities X Y) :
      1≤M 2 0*X+M 2 1*Y+M 2 2 := by
    have h := whole_polygon_denominator x hn X Y hXY
    rw [hx] at h
    simpa only [M,denominator,← affineForm_value,affineForm] using h
  have he : M 2 0*A+M 2 1*B+M 2 2=1 := by
    simpa only [M,denominator,← affineForm_value,affineForm] using heq
  have hc := origin_equality (M 2 0) (M 2 1) (M 2 2) A B hP hall he
  have hd : denominator M (0,0)=1 := by
    simpa only [denominator,← affineForm_value,affineForm,mul_zero,zero_add] using hc
  have hh : height (u • center)=2 := by
    rw [PELRealKleinSideTransport318.original_height_multiplier,
      center_coordinates.1,center_coordinates.2]
    change denominator M (0,0)*height center=2
    rw [hd,center_height,one_mul]
  exact PELNormOneBaseAction318.stabilizer_sign u center (height_two_unique _ hh)

/-- No original orbit has two different polygon representatives if at least
one lies in the STRICT original polygon. Boundary-to-boundary identification
remains a separate theorem and is not hidden in this conclusion. -/
theorem strict_representative_unique (τ : HalfPlane) (u : normOneUnits)
    (hτ : strictInequalities (scaledFirst τ) (scaledSecond τ))
    (huτ : u • τ∈originalDomain) : u • τ=τ := by
  have hw : τ∈originalDomain := weak_of_strict _ _ hτ
  have hh := polygon_orbit_height τ u hw huτ
  rw [PELRealKleinSideTransport318.original_height_multiplier] at hh
  have hd : denominator (realMatrix ((u.val:order):PELQuaternionAlgebra318.B))
      (scaledFirst τ,scaledSecond τ)=1 := by
    nlinarith [height_pos τ]
  have hs := equality_implies_sign u _ _ hτ hd
  apply Subtype.ext
  exact PELNormOneBaseAction318.sign_parameter u.val hs τ
end PELOriginalInteriorUniqueness318
