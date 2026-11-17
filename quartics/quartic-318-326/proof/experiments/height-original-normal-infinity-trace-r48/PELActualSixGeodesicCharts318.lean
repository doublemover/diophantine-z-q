module
public import PELActualEdgeHalfNeighborhood318
public section
noncomputable section
namespace PELActualSixGeodesicCharts318
open Set Filter Complex
open scoped Topology
open PELActualEdgeHalfNeighborhood318 PELMaximalActualComplexDomain318
open PELQuaternionRealRepresentation318
set_option maxHeartbeats 2800000

@[expose] def leading : Fin 6→ℝ := ![1,beta-1,30,30,35-7*beta,35-7*beta]
@[expose] def middle : Fin 6→ℝ := ![0,0,alpha*beta,-alpha*beta,alpha*beta,-alpha*beta]
@[expose] def constantTerm : Fin 6→ℝ := ![-1,-beta-1,30,30,35+7*beta,35+7*beta]
@[expose] def discriminant : Fin 6→ℝ := ![1,4,150,150,70,70]
@[expose] def orientation : Fin 6→ℝ := ![1,-1,1,1,1,1]
@[expose] def weight : Fin 6→ℝ := ![beta,1,1,1,1,1]
@[expose] def equation (i:Fin 6) (z:ℂ) : ℝ :=
  leading i*normSq z-2*middle i*z.re+constantTerm i
@[expose] def leftEndpoint (i:Fin 6) : ℝ :=
  (middle i-Real.sqrt (discriminant i))/leading i
@[expose] def rightEndpoint (i:Fin 6) : ℝ :=
  (middle i+Real.sqrt (discriminant i))/leading i

/-- The top edge reverses its flattening orientation; both LEFT circles
have their genuine negative real centers, with holomorphic (not merely
antiholomorphic mirror) charts. -/
@[expose] def straighten (i:Fin 6) (z:ℂ) : ℂ :=
  (orientation i:ℂ)*GeodesicCircleFlattening318.flatten (leftEndpoint i) (rightEndpoint i) z
@[expose] def unstraighten (i:Fin 6) (w:ℂ) : ℂ :=
  GeodesicCircleFlattening318.unflatten (leftEndpoint i) (rightEndpoint i) ((orientation i:ℂ)*w)

theorem leading_pos (i:Fin 6) : 0<leading i := by
  have hβ:1<beta := by nlinarith [beta_pos,beta_sq]
  have hβ':beta<5 := by nlinarith [beta_pos,beta_sq]
  fin_cases i <;> norm_num [leading] <;> linarith

theorem weight_pos (i:Fin 6) : 0<weight i := by
  fin_cases i <;> norm_num [weight] <;> exact beta_pos

theorem orientation_sq (i:Fin 6) : orientation i*orientation i=1 := by
  fin_cases i <;> norm_num [orientation]

theorem discriminant_pos (i:Fin 6) : 0<discriminant i := by
  fin_cases i <;> norm_num [discriminant]

theorem discriminant_identity (i:Fin 6) :
    (middle i)^2-leading i*constantTerm i=discriminant i := by
  have hab:(alpha*beta)^2=1050 := by rw [mul_pow,alpha_sq,beta_sq];norm_num
  fin_cases i <;> norm_num [middle,leading,constantTerm,discriminant] <;> nlinarith [beta_sq]

theorem endpoints_ordered (i:Fin 6) : leftEndpoint i<rightEndpoint i := by
  unfold leftEndpoint rightEndpoint
  apply (div_lt_div_iff_of_pos_right (leading_pos i)).mpr
  linarith [Real.sqrt_pos.mpr (discriminant_pos i)]

theorem endpoint_sum (i:Fin 6) : leftEndpoint i+rightEndpoint i=2*middle i/leading i := by
  unfold leftEndpoint rightEndpoint
  ring

theorem endpoint_product (i:Fin 6) : leftEndpoint i*rightEndpoint i=constantTerm i/leading i := by
  have hs:=Real.sq_sqrt (discriminant_pos i).le
  have hd:=discriminant_identity i
  unfold leftEndpoint rightEndpoint
  field_simp [(leading_pos i).ne']
  nlinarith

/-- Exact signed equations connect ALL six actual Klein inequalities to
the original complex semicircle equations. -/
theorem equation_slack (i:Fin 6) (z:ℂ) :
    weight i*orientation i*equation i z=(normSq z+1)*slack i z := by
  have hn:normSq z+1≠0 := by nlinarith [normSq_nonneg z]
  fin_cases i <;> norm_num [weight,orientation,equation,leading,middle,constantTerm,
    slack,coordinates] <;> field_simp [hn] <;> ring

theorem flatten_equation_product (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    leading i*normSq ((rightEndpoint i:ℂ)-z)*
      (GeodesicCircleFlattening318.flatten (leftEndpoint i) (rightEndpoint i) z).im=equation i z := by
  have hD:normSq ((rightEndpoint i:ℂ)-z)≠0 :=
    (normSq_pos.mpr (GeodesicCircleFlattening318.endpoint_ne _ _ hz)).ne'
  rw [GeodesicCircleFlattening318.flatten_im,endpoint_sum,endpoint_product]
  unfold equation
  field_simp [hD,(leading_pos i).ne']
  ring

theorem straighten_slack_product (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    (weight i*leading i*normSq ((rightEndpoint i:ℂ)-z))*(straighten i z).im=
      (normSq z+1)*slack i z := by
  calc
    _=weight i*orientation i*(leading i*normSq ((rightEndpoint i:ℂ)-z)*
        (GeodesicCircleFlattening318.flatten (leftEndpoint i) (rightEndpoint i) z).im) := by
      simp only [straighten,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      ring
    _=weight i*orientation i*equation i z := by rw [flatten_equation_product i z hz]
    _=_ := equation_slack i z

theorem straighten_positive_iff (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    0<(straighten i z).im ↔ 0<slack i z := by
  have hK:0<weight i*leading i*normSq ((rightEndpoint i:ℂ)-z) :=
    mul_pos (mul_pos (weight_pos i) (leading_pos i))
      (normSq_pos.mpr (GeodesicCircleFlattening318.endpoint_ne _ _ hz))
  have hN:0<normSq z+1 := by nlinarith [normSq_nonneg z]
  calc
    0<(straighten i z).im ↔ 0<(weight i*leading i*normSq ((rightEndpoint i:ℂ)-z))*(straighten i z).im :=
      (mul_pos_iff_of_pos_left hK).symm
    _ ↔ 0<(normSq z+1)*slack i z := by rw [straighten_slack_product i z hz]
    _ ↔ 0<slack i z := mul_pos_iff_of_pos_left hN

theorem straighten_real_iff (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    (straighten i z).im=0 ↔ slack i z=0 := by
  have hK:(weight i*leading i*normSq ((rightEndpoint i:ℂ)-z))≠0 :=
    (mul_pos (mul_pos (weight_pos i) (leading_pos i))
      (normSq_pos.mpr (GeodesicCircleFlattening318.endpoint_ne _ _ hz))).ne'
  have hN:normSq z+1≠0 := by nlinarith [normSq_nonneg z]
  have h:=straighten_slack_product i z hz
  constructor <;> intro he
  · rw [he,mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hN
  · rw [he,mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hK

theorem straighten_differentiableAt (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    DifferentiableAt ℂ (straighten i) z := by
  have hn:=GeodesicCircleFlattening318.endpoint_ne (rightEndpoint i) z hz
  unfold straighten GeodesicCircleFlattening318.flatten
  exact differentiableAt_const.mul (differentiableAt_const.mul
    ((differentiableAt_id.sub_const _).div (differentiableAt_const.sub differentiableAt_id) hn))

theorem unstraighten_straighten (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    unstraighten i (straighten i z)=z := by
  have ho:(orientation i:ℂ)*(orientation i:ℂ)=1 := by exact_mod_cast orientation_sq i
  simp only [unstraighten,straighten,←mul_assoc,ho,one_mul]
  exact GeodesicCircleFlattening318.unflatten_flatten _ _ (endpoints_ordered i) _
    (GeodesicCircleFlattening318.endpoint_ne _ _ hz)

theorem inverse_polefree_at_straighten (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    1+Complex.I*((orientation i:ℂ)*straighten i z)≠0 := by
  have ho:(orientation i:ℂ)*(orientation i:ℂ)=1 := by exact_mod_cast orientation_sq i
  simp only [straighten,←mul_assoc,ho,one_mul]
  exact GeodesicCircleFlattening318.one_add_flatten_ne _ _ (endpoints_ordered i) _
    (GeodesicCircleFlattening318.endpoint_ne _ _ hz)

theorem straighten_unstraighten (i:Fin 6) (w:ℂ)
    (hw:1+Complex.I*((orientation i:ℂ)*w)≠0) :
    straighten i (unstraighten i w)=w := by
  have ho:(orientation i:ℂ)*(orientation i:ℂ)=1 := by exact_mod_cast orientation_sq i
  unfold straighten unstraighten
  rw [GeodesicCircleFlattening318.flatten_unflatten _ _ (endpoints_ordered i) _ hw]
  rw [←mul_assoc,ho,one_mul]

theorem unstraighten_differentiableAt (i:Fin 6) (w:ℂ)
    (hw:1+Complex.I*((orientation i:ℂ)*w)≠0) :
    DifferentiableAt ℂ (unstraighten i) w := by
  unfold unstraighten GeodesicCircleFlattening318.unflatten
  exact (differentiableAt_const.add
    (differentiableAt_const.mul (differentiableAt_const.mul
      (differentiableAt_const.mul differentiableAt_id)))).div
    (differentiableAt_const.add (differentiableAt_const.mul
      (differentiableAt_const.mul differentiableAt_id))) hw

/-- Every actual regular edge has a genuine holomorphic half-plane
coordinate for the SAME original domain, not just an equation at its
boundary points. The interior corresponds to the upper side on all six
edges, including the reversed top and both left circles. -/
theorem actual_regular_edge_halfchart {i:Fin 6} {z:ℂ} (hz:RegularEdge i z) :
    DifferentiableAt ℂ (straighten i) z ∧
    unstraighten i (straighten i z)=z ∧
    (straighten i z).im=0 ∧
    ∀ᶠw in 𝓝 z,(w∈openDomain ↔ 0<(straighten i w).im) := by
  refine ⟨straighten_differentiableAt i z hz.1,unstraighten_straighten i z hz.1,
    (straighten_real_iff i z hz.1).mpr hz.2.1,?_⟩
  filter_upwards [original_edge_local_halfspace hz,
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz.1] with w hw hi
  exact hw.trans (straighten_positive_iff i w hi).symm
/-- The inverse chart has an actual neighborhood of the real seam on
which its UPPER side is exactly the original half-cut interior. This is
the neighborhood needed to pull the modulus-reflection theorem back to
the original complex geometry. -/
theorem actual_regular_edge_inverse_halfchart {i:Fin 6} {z:ℂ} (hz:RegularEdge i z) :
    DifferentiableAt ℂ (unstraighten i) (straighten i z) ∧
    unstraighten i (straighten i z)=z ∧
    ∀ᶠw in 𝓝 (straighten i z),(unstraighten i w∈openDomain ↔ 0<w.im) := by
  have hp:=inverse_polefree_at_straighten i z hz.1
  have hd:=unstraighten_differentiableAt i (straighten i z) hp
  have he:=unstraighten_straighten i z hz.1
  have ht:Tendsto (unstraighten i) (𝓝 (straighten i z)) (𝓝 z) := by
    simpa only [he] using hd.continuousAt.tendsto
  refine ⟨hd,he,?_⟩
  have hpol : ∀ᶠw in 𝓝 (straighten i z),1+Complex.I*((orientation i:ℂ)*w)≠0 :=
    (isOpen_ne (by fun_prop) continuous_const).mem_nhds hp
  filter_upwards [ht.eventually (actual_regular_edge_halfchart hz).2.2.2,hpol] with w hw hpw
  simpa only [straighten_unstraighten i w hpw] using hw
end PELActualSixGeodesicCharts318
