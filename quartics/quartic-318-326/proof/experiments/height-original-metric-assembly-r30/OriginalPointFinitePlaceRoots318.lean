module
public import FinitePlaceChartPairBounds318
public import IntegralValuativePointCenter318
public import ContactBicanonicalPointHeight318
public section
noncomputable section
namespace OriginalPointFinitePlaceRoots318
open NumberField ActualFinitePlaceIntegers318 ContactFinitePlaceBaseMap318
open ContactArithmeticDenominator318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
abbrev K := RationalContactPoint318.PointField c t
@[expose] def roots (i : Fin 4) : K c t :=
  RationalFourRootFiber318.root (RationalContactPoint318.parameters c t) i

/-- The signs are the specified original quotient-field roots, rather than
newly chosen roots of the same four equations. -/
theorem roots_original (i : Fin 4) : roots c t i=RationalContactPoint318.sourcePoint c t
    (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i) :=
  (RationalContactPoint318.sourcePoint_generator c t i).symm

theorem roots_square (i : Fin 4) : (roots c t i)^2=
    (((c i : ℚ)*(t-LinearContactSquareclass318.contacts i):ℚ):K c t) := by
  have h := RationalFourRootFiber318.root_square (RationalContactPoint318.parameters c t) i
  simpa only [roots,RationalContactPoint318.parameters_eq,map_ratCast] using h

variable (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1)
abbrev V := Integers v
abbrev localTwists := twists c v hv

/-- The original four roots satisfy the literal integral model's equations
under the actual finite-place inclusion, with exactly the original twists. -/
theorem local_root_equations (i : Fin 4) : (roots c t i)^2=
    algebraMap (V c t v) (K c t) (localTwists c t v hv i : V c t v)*
      ((t:K c t)-algebraMap (V c t v) (K c t) (IntegralSourceBranches318.contacts (V c t v) i)) := by
  rw [ContactFinitePlaceBaseMap318.twists_value]
  have hc : algebraMap (V c t v) (K c t) (IntegralSourceBranches318.contacts (V c t v) i)=
      (LinearContactSquareclass318.contacts i : K c t) := by
    fin_cases i <;> norm_num [IntegralSourceBranches318.contacts,LinearContactSquareclass318.contacts]
  rw [hc,map_ratCast]
  have h := roots_square c t i
  push_cast at h
  exact h

/-- The local generic source map sends every ORIGINAL marked generator to
the corresponding generator value of the original rational source point. -/
theorem local_source_generator (i : Fin 4) :
    IntegralValuativeGenericPoint318.sourceMap (V c t v) (K c t) (localTwists c t v hv)
      (t:K c t) (roots c t) (local_root_equations c t v hv)
      (IntegralOriginalRootCoordinates318.root (V c t v) (localTwists c t v hv) i)=
      RationalContactPoint318.sourcePoint c t
        (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i) := by
  rw [IntegralValuativeGenericPoint318.sourceMap_generator,roots_original]
end OriginalPointFinitePlaceRoots318
