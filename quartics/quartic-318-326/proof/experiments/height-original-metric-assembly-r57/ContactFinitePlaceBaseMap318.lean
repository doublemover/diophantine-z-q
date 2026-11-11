module
public import ActualFinitePlaceIntegers318
public section
noncomputable section
namespace ContactFinitePlaceBaseMap318
open NumberField ActualFinitePlaceIntegers318 ContactArithmeticBase318 ContactArithmeticTwists318
open ContactArithmeticDenominator318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type*} [Field K] [NumberField K]
variable (c : Fin 4 → ℚˣ) (v : FinitePlace K) (hv : v (denominator c:K)=1)

include hv in
theorem denominator_unit : IsUnit (algebraMap ℤ (Integers v) (denominator c)) := by
  refine ⟨unitOfNormOne v (denominator c:K) hv,?_⟩
  apply Subtype.ext
  rfl

/-- The explicit original arithmetic base maps into the actual finite-place
integer ring at every place outside its displayed denominator. -/
@[expose] def baseMap : Base c →+* Integers v :=
  IsLocalization.Away.lift (denominator c) (denominator_unit c v hv)
@[simp] theorem baseMap_integer (z : ℤ) :
    baseMap c v hv (algebraMap ℤ (Base c) z)=algebraMap ℤ (Integers v) z :=
  IsLocalization.Away.lift_eq _ _ z

/-- The local arithmetic-base map has the ORIGINAL rational embedding as
its generic-field map. This is equality of ring maps on the entire base. -/
theorem field_square :
    (algebraMap (Integers v) K).comp (baseMap c v hv)=
      (algebraMap ℚ K).comp (intoQ c) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator c))
  apply RingHom.ext
  intro z
  simp only [RingHom.comp_apply,baseMap_integer,intoQ_integer,map_intCast]

@[expose] def twists (i : Fin 4) : (Integers v)ˣ :=
  Units.map (baseMap c v hv).toMonoidHom (twist c i)

theorem twists_value (i : Fin 4) :
    algebraMap (Integers v) K (twists c v hv i:Integers v)=algebraMap ℚ K (c i:ℚ) := by
  have h := congrArg (fun f : Base c →+* K => f (twist c i:Base c)) (field_square c v hv)
  simpa only [RingHom.comp_apply,twists,Units.coe_map,twist_value] using h

include hv in
theorem separation_unit : IsUnit (IntegralBranchDenominatorCover318.separationInteger:Integers v) := by
  simpa only [map_intCast] using
    (ContactArithmeticBase318.separation_unit c).map (baseMap c v hv)
/-- Only finitely many actual number-field places are excluded by the
explicit arithmetic denominator. This uses its proved nonvanishing. -/
theorem excluded_places_finite :
    {w : FinitePlace K | w (denominator c:K)≠1}.Finite := by
  have hn : (denominator c:K)≠0 := by exact_mod_cast denominator_ne_zero c
  exact FinitePlace.hasFiniteMulSupport hn

end ContactFinitePlaceBaseMap318
