module
public import SelectedGeneralizedLocalizedOverlap318
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedProjectiveOverlap318
open SelectedGeneralizedLocalizedOverlap318

namespace SelectedGeneralizedGluedCarrier318

variable {R : Type*} [CommRing R]

abbrev Base (R : Type*) [CommRing R] := Spec (CommRingCat.of R)
abbrev Finite (d : Rˣ) := Spec (CommRingCat.of (FiniteChart d))
abbrev Infinity (d : Rˣ) := Spec (CommRingCat.of (Chart d))
abbrev Intersection (d : Rˣ) := Spec (CommRingCat.of (UY d))

@[expose] def intoY (d : Rˣ) : Intersection d ⟶ Infinity d :=
  Spec.map (CommRingCat.ofHom (algebraMap (Chart d) (UY d)))

instance intoY_open (d : Rˣ) : IsOpenImmersion (intoY d) :=
  IsOpenImmersion.of_isLocalization (ordinate d)

@[expose] def intoZ (d : Rˣ) : Intersection d ⟶ Finite d :=
  Spec.map (overlap d).toRingEquiv.toCommRingCatIso.inv ≫
    Spec.map (CommRingCat.ofHom (algebraMap (FiniteChart d) (UZ d)))

instance intoZ_open (d : Rˣ) : IsOpenImmersion (intoZ d) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (FiniteChart d) (UZ d)))) := IsOpenImmersion.of_isLocalization (y d)
  unfold intoZ
  infer_instance

theorem intoZ_ring (d : Rˣ) :
    intoZ d = Spec.map (CommRingCat.ofHom (toUYbase d).toRingHom) := by
  unfold intoZ
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact toUY_map d a

/-- The actual generalized cubic carrier obtained by gluing the two
genuine dehomogenized charts on their exact principal intersection. -/
abbrev Carrier (d : Rˣ) : Scheme := pushout (intoZ d) (intoY d)

@[expose] def jZ (d : Rˣ) : Finite d ⟶ Carrier d := pushout.inl _ _
@[expose] def jY (d : Rˣ) : Infinity d ⟶ Carrier d := pushout.inr _ _

instance jZ_open (d : Rˣ) : IsOpenImmersion (jZ d) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoZ d) (intoY d)) WalkingSpan.left))

instance jY_open (d : Rˣ) : IsOpenImmersion (jY d) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoZ d) (intoY d)) WalkingSpan.right))

theorem glue_over_base (d : Rˣ) :
    intoZ d ≫ Spec.algebraMap R (FiniteChart d) = intoY d ≫ Spec.algebraMap R (Chart d) := by
  rw [intoZ_ring]
  unfold intoY Spec.algebraMap
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (toUYbase d).commutes r

@[expose] def overBase (d : Rˣ) : Carrier d ⟶ Base R :=
  pushout.desc (Spec.algebraMap R (FiniteChart d)) (Spec.algebraMap R (Chart d)) (glue_over_base d)

theorem jY_over (d : Rˣ) : jY d ≫ overBase d = Spec.algebraMap R (Chart d) :=
  pushout.inr_desc ..

theorem jZ_over (d : Rˣ) : jZ d ≫ overBase d = Spec.algebraMap R (FiniteChart d) :=
  pushout.inl_desc ..

@[expose] def identitySection (d : Rˣ) : Base R ⟶ Carrier d :=
  Spec.map (CommRingCat.ofHom (origin d).toRingHom) ≫ jY d

theorem identity_over (d : Rˣ) : identitySection d ≫ overBase d = 𝟙 _ := by
  rw [identitySection,Category.assoc,jY_over]
  unfold Spec.algebraMap
  rw [← Spec.map_comp]
  have h : (origin d).toRingHom.comp (algebraMap R (Chart d)) = RingHom.id R := by
    apply RingHom.ext
    exact (origin d).commutes
  change Spec.map (CommRingCat.ofHom ((origin d).toRingHom.comp (algebraMap R (Chart d)))) = _
  rw [h]
  exact Spec.map_id _

/-- The whole glued carrier is covered by the two previously verified
open charts, not merely its characteristic-zero or reduced fiber. -/
theorem charts_cover (d : Rˣ) (p : Carrier d) :
    (∃ a, jZ d a=p) ∨ (∃ b, jY d b=p) := by
  obtain ⟨i,q,hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span (intoZ d) (intoY d)) p
  cases i with
  | none =>
    left
    refine ⟨intoZ d q,?_⟩
    change ((intoZ d) ≫ jZ d) q=p
    rw [show intoZ d ≫ jZ d =
      colimit.ι (span (intoZ d) (intoY d)) WalkingSpan.zero from
      colimit.w (span (intoZ d) (intoY d)) WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q,hq⟩
    | right => exact Or.inr ⟨q,hq⟩

end SelectedGeneralizedGluedCarrier318

#print axioms SelectedGeneralizedGluedCarrier318.identity_over
#print axioms SelectedGeneralizedGluedCarrier318.charts_cover
