module
public import OriginalUpperReesFibreTransfer318
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Localization
public section
noncomputable section

namespace OriginalR47TraitRoundKernel318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]

/-- The literal localization at the prime of the existing arithmetic base. -/
abbrev base := Spec (CommRingCat.of R)
abbrev trait := Spec (CommRingCat.of (Localization.AtPrime p))
abbrev brace : trait p ⟶ base (R:=R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))

theorem brace_flat : Flat (brace p) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (Localization.AtPrime p) p.primeCompl))

theorem brace_preimmersion : IsPreimmersion (brace p) :=
  IsPreimmersion.of_isLocalization p.primeCompl

/-- The arithmetic closed point is the marked prime itself, not a newly
chosen point over that prime. -/
theorem brace_closedPoint :
    brace p (IsLocalRing.closedPoint (Localization.AtPrime p)) =
      (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change (IsLocalRing.maximalIdeal (Localization.AtPrime p)).under R = p
  exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p

variable {X S : Scheme.{u}} (s : X ⟶ base (R:=R)) (π : S ⟶ X)

abbrev restricted := pullback s (brace p)
abbrev forgetMap : restricted p s ⟶ X := pullback.fst s (brace p)
abbrev toTrait : restricted p s ⟶ trait p := pullback.snd s (brace p)

/-- Localize the given modification, preserving it as the left-hand
object of the pullback. No traitwise modification is chosen. -/
abbrev Yp := pullback π (forgetMap p s)
abbrev a : Yp p s π ⟶ restricted p s := pullback.snd π (forgetMap p s)
abbrev b : Yp p s π ⟶ S := pullback.fst π (forgetMap p s)

theorem pullback_round :
    IsPullback (b p s π) (a p s π) π (forgetMap p s) :=
  IsPullback.of_hasPullback _ _

/-- The same localized round can also be computed directly over the
structural map of its source. The comparison preserves both projections. -/
def restrictedRoundIso : Yp p s π ≅ restricted p (π ≫ s) :=
  pullbackRightPullbackFstIso s (brace p) π

@[reassoc] theorem restrictedRoundIso_old :
    (restrictedRoundIso p s π).hom ≫ forgetMap p (π ≫ s) = b p s π :=
  pullbackRightPullbackFstIso_hom_fst s (brace p) π

@[reassoc] theorem restrictedRoundIso_trait :
    (restrictedRoundIso p s π).hom ≫ toTrait p (π ≫ s) =
      a p s π ≫ toTrait p s :=
  pullbackRightPullbackFstIso_hom_snd s (brace p) π

theorem forgetMap_flat : Flat (forgetMap p s) := by
  let : Flat (brace p) := brace_flat p
  exact (inferInstance : Flat (pullback.fst s (brace p)))

theorem b_flat : Flat (b p s π) := by
  let : Flat (forgetMap p s) := forgetMap_flat p s
  exact (inferInstance : Flat (pullback.fst π (forgetMap p s)))

theorem forgetMap_preimmersion : IsPreimmersion (forgetMap p s) := by
  let : IsPreimmersion (brace p) := brace_preimmersion p
  exact (inferInstance : IsPreimmersion (pullback.fst s (brace p)))

theorem b_preimmersion : IsPreimmersion (b p s π) := by
  let : IsPreimmersion (forgetMap p s) := forgetMap_preimmersion p s
  exact (inferInstance : IsPreimmersion (pullback.fst π (forgetMap p s)))

/-- The stalk map is injective by local faithful flatness and surjective
by preimmersion. This uses the existing local stalk map, not a new
identification of fraction fields. -/
theorem stalk_iso_of_flat_preimmersion {U V : Scheme.{u}} (f : U ⟶ V)
    [Flat f] [IsPreimmersion f] (x : U) : IsIso (f.stalkMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_, f.stalkMap_surjective x⟩
  -- Same faithfully-flat local argument as Mathlib's Flat.epi_of_flat_of_surjective.
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (V.presheaf.stalk (f x)) (U.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

theorem b_stalk (x : Yp p s π) : IsIso ((b p s π).stalkMap x) := by
  let : Flat (b p s π) := b_flat p s π
  let : IsPreimmersion (b p s π) := b_preimmersion p s π
  exact stalk_iso_of_flat_preimmersion (b p s π) x

section Chart
variable {C V : Scheme.{u}} {j : C ⟶ X} {f : V ⟶ C} {g : V ⟶ S}

/-- Restrict the existing affine chart itself to the same arithmetic
localization. Its base morphism is the stock localized chart projection. -/
abbrev chartBase (j : C ⟶ X) := pullback j (forgetMap p s)
abbrev chartBaseOld (j : C ⟶ X) : chartBase p s j ⟶ C :=
  pullback.fst j (forgetMap p s)
abbrev chartBaseTrait (j : C ⟶ X) : chartBase p s j ⟶ restricted p s :=
  pullback.snd j (forgetMap p s)
abbrev chartRound (j : C ⟶ X) (f : V ⟶ C) := pullback f (chartBaseOld p s j)

def chartBaseIso (j : C ⟶ X) : chartBase p s j ≅ restricted p (j ≫ s) :=
  pullbackRightPullbackFstIso s (brace p) j

@[reassoc] theorem chartBaseIso_old (j : C ⟶ X) :
    (chartBaseIso p s j).hom ≫ forgetMap p (j ≫ s) = chartBaseOld p s j :=
  pullbackRightPullbackFstIso_hom_fst s (brace p) j

/-- Localize a supplied genuine Rees-chart square of the original round.
Pasting the old chart with the actual localization constructs the new
chart map and its Cartesian square, preserving the old chart arrow. -/
theorem localize_chart (h : IsPullback g f π j) :
    ∃ l : chartRound p s j f ⟶ Yp p s π,
      IsPullback l (pullback.snd f (chartBaseOld p s j)) (a p s π) (chartBaseTrait p s j) ∧
      l ≫ b p s π = pullback.fst f (chartBaseOld p s j) ≫ g := by
  have hp := (IsPullback.of_hasPullback f (chartBaseOld p s j)).paste_horiz h
  have hc : chartBaseOld p s j ≫ j = chartBaseTrait p s j ≫ forgetMap p s :=
    pullback.condition
  have houter : IsPullback (pullback.fst f (chartBaseOld p s j) ≫ g)
      (pullback.snd f (chartBaseOld p s j)) π (chartBaseTrait p s j ≫ forgetMap p s) := by
    rw [← hc]
    exact hp
  let hr := pullback_round p s π
  have hw : pullback.fst f (chartBaseOld p s j) ≫ g ≫ π =
      (pullback.snd f (chartBaseOld p s j) ≫ chartBaseTrait p s j) ≫ forgetMap p s := by
    simpa only [Category.assoc] using houter.w
  refine ⟨hr.lift (pullback.fst f (chartBaseOld p s j) ≫ g)
    (pullback.snd f (chartBaseOld p s j) ≫ chartBaseTrait p s j) hw, ?_, ?_⟩
  · exact houter.of_right' hr
  · exact hr.lift_fst _ _ _

end Chart

/-- Every existing point over the marked base prime has a unique lift
over the actual closed point of its localization. -/
theorem lift_at_prime (x : X) (hx : s x = (⟨p, inferInstance⟩ : PrimeSpectrum R)) :
    ∃! y : restricted p s, forgetMap p s y = x ∧
      toTrait p s y = IsLocalRing.closedPoint (Localization.AtPrime p) := by
  let t := IsLocalRing.closedPoint (Localization.AtPrime p)
  have he : s x = brace p t := hx.trans (brace_closedPoint p).symm
  obtain ⟨y, hyx, hyt⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback s (brace p)) x t he
  let : IsPreimmersion (forgetMap p s) := forgetMap_preimmersion p s
  refine ⟨y, ⟨hyx, hyt⟩, ?_⟩
  intro z hz
  exact (forgetMap p s).isEmbedding.injective (hz.1.trans hyx.symm)

/-- Localize an existing marked section, without a new point choice. -/
def retained (Q : base (R:=R) ⟶ X) (hQ : Q ≫ s = 𝟙 _) :
    trait p ⟶ restricted p s :=
  pullback.lift (brace p ≫ Q) (𝟙 _) (by simp only [Category.assoc, hQ, Category.comp_id, Category.id_comp])

@[reassoc] theorem retained_old (Q : base (R:=R) ⟶ X) (hQ : Q ≫ s = 𝟙 _) :
    retained p s Q hQ ≫ forgetMap p s = brace p ≫ Q := by
  exact pullback.lift_fst _ _ _

@[reassoc] theorem retained_trait (Q : base (R:=R) ⟶ X) (hQ : Q ≫ s = 𝟙 _) :
    retained p s Q hQ ≫ toTrait p s = 𝟙 _ := by
  exact pullback.lift_snd _ _ _

/-- If the given proper round already carries the marked section, its
localization is the same section on the actual localized round. -/
def retainedRound (Q : base (R:=R) ⟶ S) (hQ : Q ≫ π ≫ s = 𝟙 _) :
    trait p ⟶ Yp p s π :=
  pullback.lift (brace p ≫ Q)
    (retained p s (Q ≫ π) (by simpa only [Category.assoc] using hQ)) (by
      rw [retained_old, Category.assoc])

@[reassoc] theorem retainedRound_old (Q : base (R:=R) ⟶ S) (hQ : Q ≫ π ≫ s = 𝟙 _) :
    retainedRound p s π Q hQ ≫ b p s π = brace p ≫ Q :=
  pullback.lift_fst _ _ _

@[reassoc] theorem retainedRound_down (Q : base (R:=R) ⟶ S) (hQ : Q ≫ π ≫ s = 𝟙 _) :
    retainedRound p s π Q hQ ≫ a p s π =
      retained p s (Q ≫ π) (by simpa only [Category.assoc] using hQ) :=
  pullback.lift_snd _ _ _

section LiteralR40
variable {A : Type} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  (𝔭 : Ideal A) [𝔭.IsPrime] (q : A) (d : ℕ)

abbrev literalStructure :
    Spec (CommRingCat.of (OriginalThickCentralReesChart318.O q d)) ⟶ base (R:=A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (OriginalThickCentralReesChart318.O q d)))

/-- A genuine specialization: the round is the strict literal R40
blowup, and its localized point lies over the actual old centre ideal.
No connectedness or replacement local Rees chart is given. -/
theorem literal_localized_fibre (hq : Irreducible q)
    (x : restricted 𝔭 (literalStructure q d))
    (hx : (forgetMap 𝔭 (literalStructure q d) x).asIdeal =
      OriginalThickCentralReesChart318.I q d) :
    _root_.IsConnected ((a 𝔭 (literalStructure q d)
        (OriginalUpperR40SplitFieldFibre318.toOld q d)) ⁻¹'
      ({x} : Set (restricted 𝔭 (literalStructure q d)))) :=
  OriginalUpperReesFibreTransfer318.split_connected_in_square q hq d
    (pullback_round 𝔭 (literalStructure q d)
      (OriginalUpperR40SplitFieldFibre318.toOld q d)) x hx

end LiteralR40

end OriginalR47TraitRoundKernel318

#print axioms OriginalR47TraitRoundKernel318.brace_closedPoint
#print axioms OriginalR47TraitRoundKernel318.pullback_round
#print axioms OriginalR47TraitRoundKernel318.restrictedRoundIso_old
#print axioms OriginalR47TraitRoundKernel318.restrictedRoundIso_trait
#print axioms OriginalR47TraitRoundKernel318.b_stalk
#print axioms OriginalR47TraitRoundKernel318.lift_at_prime
#print axioms OriginalR47TraitRoundKernel318.retainedRound_old
#print axioms OriginalR47TraitRoundKernel318.retainedRound_down
#print axioms OriginalR47TraitRoundKernel318.chartBaseIso_old
#print axioms OriginalR47TraitRoundKernel318.localize_chart
#print axioms OriginalR47TraitRoundKernel318.literal_localized_fibre
