module
public import OriginalAllPlaceRootBounds318
public import ContactOriginalMetricConsumer318
public section
noncomputable section
namespace OriginalContactAllPlaceSpecialization318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0)
abbrev t : ℚ := ContactOriginalMetricConsumer318.coordinate u v
abbrev Field := K c (t u v)

/-- The chosen local data contain the SAME original point-field roots. The
choice is only of uniformizers, square normalizations and actual extensions. -/
@[expose] def localData (w : FinitePlace (Field c u v)) : Data c (t u v) w :=
  Classical.choose (exists_center c (t u v) w)
@[expose] def center (w : FinitePlace (Field c u v)) :
    Spec (CommRingCat.of (V c (t u v) w)) ⟶ (localData c u v w).model :=
  Classical.choose (Classical.choose_spec (exists_center c (t u v) w))

theorem center_over_base (w : FinitePlace (Field c u v)) :
    center c u v w ≫ (localData c u v w).structureMap = 𝟙 _ :=
  (Classical.choose_spec (Classical.choose_spec (exists_center c (t u v) w))).1

theorem center_generic (w : FinitePlace (Field c u v)) :
    Spec.map (CommRingCat.ofHom (algebraMap (V c (t u v) w) (Field c u v))) ≫
      center c u v w = (localData c u v w).genericPoint :=
  (Classical.choose_spec (Classical.choose_spec (exists_center c (t u v) w))).2

theorem point_field_degree : Module.finrank ℚ (Field c u v) ≤ 16 :=
  RationalContactPoint318.point_field_degree_le c (t u v)

/-- Every coordinate is the actual source-generator value, and is nonzero
from precisely the original five-form avoidance hypothesis. -/
theorem signed_root_nonzero (i : Fin 4) : roots c (t u v) i ≠ 0 :=
  RationalContactPoint318.roots_ne_of_forms c u v hf i

theorem signed_root_bound (w : FinitePlace (Field c u v)) (i : Fin 4) :
    w (RationalContactPoint318.sourcePoint c (t u v)
      (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i)) ≤
    w ((localData c u v w).multiplier i) * max 1 (w (t u v : Field c u v)) := by
  rw [←roots_original]
  exact OriginalAllPlaceRootBounds318.original_root_bound c (t u v) w (localData c u v w) i

/-- The actual global section pair is retained alongside the all-place
model construction. This does not confuse the constructed singular model
with a regular model or identify its roots with a cotangent frame. -/
theorem same_original_section_ratio (i : Fin 4) :
    ContactBicanonicalPointHeight318.a0 c (t u v)
      (RationalContactPoint318.parameters_ne_of_forms c u v hf) i ≠ 0 ∧
    ContactBicanonicalPointHeight318.a1 c (t u v)
      (RationalContactPoint318.parameters_ne_of_forms c u v hf) i =
      (t u v : Field c u v) * ContactBicanonicalPointHeight318.a0 c (t u v)
        (RationalContactPoint318.parameters_ne_of_forms c u v hf) i :=
  ⟨ContactBicanonicalPointHeight318.a0_ne _ _ _ _,
    ContactBicanonicalPointHeight318.ratio _ _ _ _⟩
end OriginalContactAllPlaceSpecialization318
