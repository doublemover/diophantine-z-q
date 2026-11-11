module
public import OriginalAllPrimeGenericPoint318
public import OriginalContactAllPlaceSpecialization318
public section
noncomputable section
namespace OriginalContactAllPrimeNeighborhood318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPrimeZoomInput318
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0)
abbrev coordinate : ℚ := ContactOriginalMetricConsumer318.coordinate u v
abbrev Field := K c (coordinate u v)
variable (w : FinitePlace (Field c u v))
abbrev data := OriginalContactAllPlaceSpecialization318.localData c u v w

@[expose] def mode : Mode := Classical.choose
  (exists_input c (coordinate u v) w (data c u v w)
    (RationalContactPoint318.parameters_ne_of_forms c u v hf))
@[expose] def input : Input c (coordinate u v) w (data c u v w) (mode c u v hf w) :=
  Classical.choice (Classical.choose_spec
    (exists_input c (coordinate u v) w (data c u v w)
      (RationalContactPoint318.parameters_ne_of_forms c u v hf)))
abbrev Chart := (input c u v hf w).Chart
abbrev SourceOpen := OriginalAllPrimeGenericComparison318.OriginalOpen
  c (coordinate u v) w (data c u v w) (m:=mode c u v hf w)
abbrev GenericChart := (Field c u v) ⊗[V c (coordinate u v) w] Chart c u v hf w

/-- No good-prime, odd-residue-characteristic, even-twist or contact-
separation premise remains: every actual finite place has this chart. -/
theorem smooth : Algebra.Smooth (V c (coordinate u v) w) (Chart c u v hf w) :=
  (input c u v hf w).smooth
@[expose] def point : Chart c u v hf w →+* V c (coordinate u v) w :=
  (input c u v hf w).point
@[expose] def genericEquivalence : SourceOpen c u v hf w ≃ₐ[Field c u v] GenericChart c u v hf w :=
  OriginalAllPrimeGenericComparison318.algebraEquivalence
    c (coordinate u v) w (data c u v w) (input c u v hf w)
@[expose] def genericEvaluation : GenericChart c u v hf w →ₐ[Field c u v] Field c u v :=
  OriginalAllPrimeGenericPoint318.genericEvaluation
    c (coordinate u v) w (data c u v w) (input c u v hf w)

theorem point_over_base (r : V c (coordinate u v) w) :
    point c u v hf w (algebraMap (V c (coordinate u v) w) (Chart c u v hf w) r)=r :=
  IntegralZoomNeighborhood318.point_scalar _ _ _ _ _ r

theorem field_degree : Module.finrank ℚ (Field c u v)≤16 :=
  OriginalContactAllPlaceSpecialization318.point_field_degree c u v

theorem same_original_signed_root (i : Fin 4) :
    (match mode c u v hf w with
      | .finite => (data c u v w).multiplier i
      | .reciprocal => (data c u v w).multiplier i*(coordinate u v : Field c u v))*
      genericEvaluation c u v hf w
        (genericEquivalence c u v hf w
          (algebraMap _ (SourceOpen c u v hf w)
            (FourRootOrderSigns318.generator
              (OriginalAllPrimeGenericComparison318.genericCoefficients
                c (coordinate u v) w (data c u v w) (m:=mode c u v hf w)) i)))=
      RationalContactPoint318.sourcePoint c (coordinate u v)
        (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i) := by
  rw [←roots_original]
  exact OriginalAllPrimeGenericPoint318.recovered_original_root
    c (coordinate u v) w (data c u v w) (input c u v hf w) i

/-- The original global pair and original height consumer are unchanged.
Smoothness of these point neighborhoods is not a replacement for the
missing global arithmetic dualizing/Hodge/Kodaira-Spencer comparison. -/
theorem same_original_section_pair (i : Fin 4) :
    ContactBicanonicalPointHeight318.a0 c (coordinate u v)
      (RationalContactPoint318.parameters_ne_of_forms c u v hf) i≠0 ∧
    ContactBicanonicalPointHeight318.a1 c (coordinate u v)
      (RationalContactPoint318.parameters_ne_of_forms c u v hf) i=
      (coordinate u v : Field c u v)*ContactBicanonicalPointHeight318.a0 c (coordinate u v)
        (RationalContactPoint318.parameters_ne_of_forms c u v hf) i :=
  OriginalContactAllPlaceSpecialization318.same_original_section_ratio c u v hf i
end OriginalContactAllPrimeNeighborhood318
