module
public import InfinityCrossMaps318
public section
noncomputable section
namespace MixedDenominator318
set_option maxHeartbeats 500000
variable {R:Type u} [CommRing R]

/-- If a homogeneous output numerator and another proportional slope denominator are units,
then the first denominator is already a unit. No reducedness or density is used. -/
theorem denominator_unit (x y z d e D E:R) (h:e*D=E*d)
    (hD:IsUnit D) (hV:IsUnit (e*(x*d^2-(e^2-(x+z)*d^2))-y*d^3)) : IsUnit d := by
  let k:R:=↑hD.unit⁻¹
  have hk:k*D=1 := by
    rw [←hD.unit_spec]
    exact Units.inv_mul _
  have he : (E*k)*d=e := by
    apply hD.mul_right_cancel
    calc
      _=(E*d)*(k*D) := by ring
      _=e*D := by rw [hk,mul_one,h]
  have hdv : d ∣ e*(x*d^2-(e^2-(x+z)*d^2))-y*d^3 := by
    refine ⟨d^2*((E*k)*(2*x+z-(E*k)^2)-y),?_⟩
    rw [←he]
    ring
  exact isUnit_of_dvd_unit hdv hV

open InfinityAdditionAlgebra318
variable {S:Type u} [CommRing S] [Algebra R S]

/-- At either actual infinity-output chart, invertibility of the other denominator forces
invertibility of its own denominator. This is the exact mixed-overlap refinement. -/
theorem actual_denominator_unit (A B:R) (t:Bool) (φ:OutputRing A B t →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B t (InfinityAdditionAlgebra318.denominator A B (!t))))) :
    IsUnit (φ (pairMap A B t (InfinityAdditionAlgebra318.denominator A B t))) := by
  let f:=φ.comp (pairMap A B t)
  have hv:=((numeratorY_unit A B t).map φ)
  have hp:=congrArg f (HomogeneousCross318.actual_cross A B)
  simp only [map_sub,map_mul,map_zero] at hp
  have hp' : f (slopeNumerator A B t)*f (InfinityAdditionAlgebra318.denominator A B (!t))=
      f (slopeNumerator A B (!t))*f (InfinityAdditionAlgebra318.denominator A B t) := by
    cases t
    · exact sub_eq_zero.mp hp
    · exact (sub_eq_zero.mp hp).symm
  change IsUnit (f (InfinityAdditionAlgebra318.denominator A B (!t))) at hd
  change IsUnit (f (numeratorY A B t)) at hv
  simp only [numeratorY,numeratorX,map_sub,map_mul,map_add,InfinityAdditionFinite318.pair_pow] at hv
  exact denominator_unit _ _ _ _ _ _ _ hp' hd hv

end MixedDenominator318
