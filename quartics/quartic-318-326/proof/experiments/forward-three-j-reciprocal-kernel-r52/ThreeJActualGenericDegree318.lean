module
public import ThreeJActualDominance318
public import Mathlib.LinearAlgebra.Dimension.Localization
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.RingTheory.OreLocalization.Ring
public section
noncomputable section
namespace ThreeJActualGenericDegree318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJMonicAlgebra318 ThreeJLaurentEquiv318
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Projective := ProjectiveJLine318.scheme ℚ

local instance (priority := 2000) : Algebra Base Laurent := ThreeJFiniteLaurentMap318.jAlgebra
/-- Pin the SAME j-coordinate module, not the Laurent localization's
unrelated native polynomial-coordinate action. -/
local instance (priority := 2000) : Module Base Laurent := ThreeJFiniteLaurentMap318.jAlgebra.toModule
local instance (priority := 2000) : SMul Base Laurent := ThreeJFiniteLaurentMap318.jAlgebra.toSMul
local instance (priority := 2000) : FaithfulSMul Base Laurent :=
  (faithfulSMul_iff_algebraMap_injective Base Laurent).mpr ThreeJActualDominance318.baseMap_injective

/-- The actual scalar map on fractions is explicitly j followed by the
original Laurent inclusion. No ambient T-coordinate algebra is inferred. -/
@[expose,instance_reducible] def jFractionAlgebra : Algebra Base (FractionRing Laurent) :=
  ((algebraMap Laurent (FractionRing Laurent)).comp
    ThreeJLaurentEquiv318.baseMap.toRingHom).toAlgebra
attribute [local instance] jFractionAlgebra
local instance (priority := 2000) : Module Base (FractionRing Laurent) := jFractionAlgebra.toModule
local instance (priority := 2000) : SMul Base (FractionRing Laurent) := jFractionAlgebra.toSMul
local instance (priority := 2000) : IsScalarTower Base Laurent (FractionRing Laurent) :=
  IsScalarTower.of_algebraMap_eq' (R:=Base) (S:=Laurent) (A:=FractionRing Laurent) rfl
local instance (priority := 2000) : FaithfulSMul Base (FractionRing Laurent) :=
  (faithfulSMul_iff_algebraMap_injective Base (FractionRing Laurent)).mpr
    ((IsFractionRing.injective Laurent (FractionRing Laurent)).comp
      ThreeJActualDominance318.baseMap_injective)
local instance (priority := 2000) : Algebra (FractionRing Base) (FractionRing Laurent) :=
  FractionRing.liftAlgebra Base (FractionRing Laurent)
local instance (priority := 2000) : Module (FractionRing Base) (FractionRing Laurent) :=
  (FractionRing.liftAlgebra Base (FractionRing Laurent)).toModule
local instance (priority := 2000) : SMul (FractionRing Base) (FractionRing Laurent) :=
  (FractionRing.liftAlgebra Base (FractionRing Laurent)).toSMul
local instance (priority := 2000) : IsScalarTower Base (FractionRing Base) (FractionRing Laurent) :=
  FractionRing.isScalarTower_liftAlgebra Base (FractionRing Laurent)

local instance (priority := 2000) : IsDominant (Spec.map (CommRingCat.ofHom ThreeJLaurentEquiv318.baseMap.toRingHom)) :=
  ThreeJActualDominance318.affine_dominant

@[expose,instance_reducible] def sourceAlgebra : Algebra Laurent Projective.functionField :=
  ActualOpenFractionField318.sourceAlgebra ProjectiveLineOverlap318.embedding
@[expose,instance_reducible] def targetAlgebra : Algebra Base Projective.functionField :=
  ActualOpenFractionField318.sourceAlgebra (JLineAtlas318.chart ℚ 1)
attribute [local instance] sourceAlgebra targetAlgebra

@[expose] def sourceEquiv : Projective.functionField ≃ₐ[Laurent] FractionRing Laurent :=
  ActualOpenFractionField318.equiv ProjectiveLineOverlap318.embedding (FractionRing Laurent)
@[expose] def targetEquiv : Projective.functionField ≃ₐ[Base] FractionRing Base :=
  ActualOpenFractionField318.equiv (JLineAtlas318.chart ℚ 1) (FractionRing Base)

/-- The actual generic-stalk pullback of the exact global projective j map. -/
@[expose] def pullback : Projective.functionField ⟶ Projective.functionField :=
  DominantFunctionField318.map ThreeProjectiveJMap318.map
lemma pullback_on_base (a : Base) :
    pullback (algebraMap Base Projective.functionField a)=
      algebraMap Laurent Projective.functionField (ThreeJLaurentEquiv318.baseMap a) :=
  OpenFunctionFieldSquare318.on_coefficient ProjectiveLineOverlap318.embedding
    (JLineAtlas318.chart ℚ 1) ThreeProjectiveJMap318.map
    ThreeJLaurentEquiv318.baseMap.toRingHom ThreeJFiniteLaurentMap318.original_scheme_square a

/-- Equality of the complete generic-stalk map with the explicit compatible
fraction-field inclusion, not just equality on the j generator or a degree count. -/
theorem actual_field_square : sourceEquiv.toRingHom.comp pullback.hom=
    (algebraMap (FractionRing Base) (FractionRing Laurent)).comp targetEquiv.toRingHom := by
  letI : IsFractionRing Base Projective.functionField :=
    ActualOpenFractionField318.fractionRing (JLineAtlas318.chart ℚ 1)
  apply IsLocalization.ringHom_ext Base⁰
  apply RingHom.ext
  intro a
  change sourceEquiv (pullback (algebraMap Base Projective.functionField a))=
    algebraMap (FractionRing Base) (FractionRing Laurent)
      (targetEquiv (algebraMap Base Projective.functionField a))
  rw [pullback_on_base,sourceEquiv.commutes,targetEquiv.commutes,
    ←IsScalarTower.algebraMap_apply Base (FractionRing Base),
    IsScalarTower.algebraMap_apply Base Laurent]
  rfl

lemma laurent_fraction_degree_four :
    Module.finrank (FractionRing Base) (FractionRing Laurent)=4 := by
  letI : Module.Finite Base Laurent := ThreeJFiniteLaurentMap318.laurent_finite_free.1
  rw [IsFractionRing.finrank_eq Base (FractionRing Base) Laurent (FractionRing Laurent)]
  exact ThreeJFiniteLaurentMap318.laurent_rank_four

@[expose,instance_reducible] def pullbackAlgebra :
    Algebra Projective.functionField Projective.functionField := pullback.hom.toAlgebra
attribute [local instance] pullbackAlgebra

/-- Degree four for the actual global scheme morphism's actual generic-point
stalk pullback. The scalar action is explicitly the original map, not an
abstract degree-four field extension selected independently of the scheme. -/
theorem actual_generic_degree_four :
    letI := pullbackAlgebra
    letI : Module Projective.functionField Projective.functionField := pullbackAlgebra.toModule
    Module.finrank Projective.functionField Projective.functionField=4 := by
  letI := pullbackAlgebra
  letI : Module Projective.functionField Projective.functionField := pullbackAlgebra.toModule
  letI : SMul Projective.functionField Projective.functionField := pullbackAlgebra.toSMul
  have hc : (algebraMap (FractionRing Base) (FractionRing Laurent)).comp targetEquiv.toRingHom=
      sourceEquiv.toRingHom.comp (algebraMap Projective.functionField Projective.functionField) :=
    actual_field_square.symm
  exact (Algebra.finrank_eq_of_equiv_equiv targetEquiv.toRingEquiv sourceEquiv.toRingEquiv hc).trans
    laurent_fraction_degree_four

end ThreeJActualGenericDegree318
