module
public import LegendreInvariantChartUnits318
public section
noncomputable section
namespace LegendreDifferentialReparametrization318
open Filter
open scoped Topology
open LegendreInvariantTangent318 LegendreInvariantAnalytic318

lemma finite_scale (l x y dx dy a : ℂ) :
    finiteValue l x y (dx*a) (dy*a)=finiteValue l x y dx dy*a := by
  unfold finiteValue
  split <;> ring
lemma infinity_scale (l u v du dv a : ℂ) :
    infinityValue l u v (du*a) (dv*a)=infinityValue l u v du dv*a := by
  unfold infinityValue
  split <;> ring

/-- Genuine chain rule along an actual local reparametrization, with both
coordinate identities asserted on a neighborhood, not merely at a point. -/
lemma finite_reparam (l : ℂ) (x y X Y t : ℂ→ℂ) (z : ℂ)
    (hX : DifferentiableAt ℂ X (t z)) (hY : DifferentiableAt ℂ Y (t z))
    (ht : DifferentiableAt ℂ t z)
    (hx : ∀ᶠ w in 𝓝 z,x w=X (t w)) (hy : ∀ᶠ w in 𝓝 z,y w=Y (t w)) :
    finiteCoefficient l x y z=finiteCoefficient l X Y (t z)*deriv t z := by
  have hdx : deriv x z=deriv X (t z)*deriv t z :=
    ((hX.hasDerivAt.comp z ht.hasDerivAt).congr_of_eventuallyEq hx).deriv
  have hdy : deriv y z=deriv Y (t z)*deriv t z :=
    ((hY.hasDerivAt.comp z ht.hasDerivAt).congr_of_eventuallyEq hy).deriv
  unfold finiteCoefficient
  rw [hx.self_of_nhds,hy.self_of_nhds,hdx,hdy,finite_scale]
lemma infinity_reparam (l : ℂ) (u v U V t : ℂ→ℂ) (z : ℂ)
    (hU : DifferentiableAt ℂ U (t z)) (hV : DifferentiableAt ℂ V (t z))
    (ht : DifferentiableAt ℂ t z)
    (hu : ∀ᶠ w in 𝓝 z,u w=U (t w)) (hv : ∀ᶠ w in 𝓝 z,v w=V (t w)) :
    infinityCoefficient l u v z=infinityCoefficient l U V (t z)*deriv t z := by
  have hdu : deriv u z=deriv U (t z)*deriv t z :=
    ((hU.hasDerivAt.comp z ht.hasDerivAt).congr_of_eventuallyEq hu).deriv
  have hdv : deriv v z=deriv V (t z)*deriv t z :=
    ((hV.hasDerivAt.comp z ht.hasDerivAt).congr_of_eventuallyEq hv).deriv
  unfold infinityCoefficient
  rw [hu.self_of_nhds,hv.self_of_nhds,hdu,hdv,infinity_scale]

variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]
/-- Reciprocal coordinate change on the SAME actual equation. This proves
compatibility of path derivatives including the forced infinity minus sign. -/
lemma reciprocal_path (u v : ℂ→ℂ) (z : ℂ)
    (hu : DifferentiableAt ℂ u z) (hv : DifferentiableAt ℂ v z)
    (hv0 : v z≠0)
    (he : ∀ᶠ w in 𝓝 z,LegendreIndependentGraphs318.infinityEquation l (u w,v w)=0) :
    finiteCoefficient l (fun w=>u w/v w) (fun w=>1/v w) z=
      infinityCoefficient l u v z := by
  have hdx := (hu.hasDerivAt.div hv.hasDerivAt hv0).deriv
  have hdy := ((hasDerivAt_const z (1:ℂ)).div hv.hasDerivAt hv0).deriv
  have hd := infinity_derivative l u v hu hv he
  unfold finiteCoefficient infinityCoefficient
  rw [hdx,hdy]
  simp only [zero_mul,one_mul,zero_sub]
  exact actual_overlap l ⟨(u z,v z),he.self_of_nhds⟩ hv0 (deriv u z) (deriv v z) hd
end LegendreDifferentialReparametrization318
