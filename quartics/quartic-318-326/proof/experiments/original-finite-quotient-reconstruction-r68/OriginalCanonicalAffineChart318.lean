module
public import OriginalNormalCoverSections318
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public section
noncomputable section
namespace OriginalCanonicalAffineChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsIntegralHom p] [IsDominant p]

/-- The literal entire base change of the old quotient along the old finite
projective chart. No affine model or chart is provided as an extra input. -/
abbrev Chart := pullback (JLineAtlas318.chart ℚ 1) p
abbrev projection : Chart p ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  pullback.fst (JLineAtlas318.chart ℚ 1) p
abbrev inclusion : Chart p ⟶ Y := pullback.snd (JLineAtlas318.chart ℚ 1) p

instance chart_affine : IsAffine (Chart p) :=
  isAffine_of_isAffineHom (projection p)
instance inclusion_open : IsOpenImmersion (inclusion p) := by
  dsimp [inclusion]
  infer_instance
instance chart_nonempty : Nonempty (Chart p) := by
  letI : Surjective p :=
    surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  obtain ⟨x, _⟩ := (projection p).surjective
    (genericPoint (Spec (CommRingCat.of (Polynomial ℚ))))
  exact ⟨x⟩
instance chart_integral : IsIntegral (Chart p) :=
  isIntegral_of_isOpenImmersion (inclusion p)

abbrev Ring := Γ(Chart p, ⊤)
instance ring_domain : IsDomain (Ring p) := inferInstance

@[expose] def chart : Spec (CommRingCat.of (Ring p)) ⟶ Y :=
  (Chart p).isoSpec.inv ≫ inclusion p
instance chart_open : IsOpenImmersion (chart p) := by
  unfold chart
  infer_instance

/-- The exact ring map of the original Cartesian projection under its
canonical affine isomorphism. Full faithfulness fixes this map uniquely. -/
@[expose] def coefficient : Polynomial ℚ →+* Ring p :=
  (Scheme.Spec.preimage ((Chart p).isoSpec.inv ≫ projection p)).unop.hom
lemma coefficient_spec : Spec.map (CommRingCat.ofHom (coefficient p)) =
    (Chart p).isoSpec.inv ≫ projection p :=
  Scheme.Spec.map_preimage _

lemma square : IsPullback (Spec.map (CommRingCat.ofHom (coefficient p)))
    (chart p) (JLineAtlas318.chart ℚ 1) p := by
  have h : Spec.map (CommRingCat.ofHom (coefficient p)) ≫ JLineAtlas318.chart ℚ 1 =
      chart p ≫ p := by
    rw [coefficient_spec]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (Chart p).isoSpec.inv ≫ k) (pullback.condition (f := JLineAtlas318.chart ℚ 1) (g := p))).trans
        (Category.assoc _ _ _).symm)
  exact IsPullback.of_iso_pullback ⟨h⟩ (Chart p).isoSpec.symm
    (coefficient_spec p).symm rfl

variable {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))
include hcover hnormal in
/-- Normality of this whole canonical Cartesian chart follows from the
old normal cover through the original open-immersion stalk maps. -/
theorem ring_normal : IsIntegrallyClosed (Ring p) := by
  obtain ⟨x⟩ := chart_nonempty p
  letI : Nonempty (⊤ : (Chart p).Opens) := ⟨⟨x, by trivial⟩⟩
  exact OriginalNormalCoverSections318.sections_of_stalks
    (OriginalNormalCoverSections318.open_stalk V hcover hnormal (inclusion p))
    ⊤ (isAffineOpen_top (Chart p))
end OriginalCanonicalAffineChart318
