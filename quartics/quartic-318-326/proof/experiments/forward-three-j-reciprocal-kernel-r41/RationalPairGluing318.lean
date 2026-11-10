module
public import RationalPairLocalMaps318
public import ThreeProjectiveJCertificates318
public section
noncomputable section
namespace RationalPairGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open RationalPairLocalMaps318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (f g : ℚ[X])

theorem chart_ranges_cover (h : IsCoprime f g) :
    (numeratorBase f).opensRange ⊔ (denominatorBase g).opensRange = ⊤ := by
  have hf : (numeratorBase f).opensRange = PrimeSpectrum.basicOpen f := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range _ _
  have hg : (denominatorBase g).opensRange = PrimeSpectrum.basicOpen g := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range _ _
  rw [hf,hg]
  exact ThreeProjectiveJCertificates318.basicOpen_cover_of_coprime h

@[expose] def chart : Bool → Scheme
  | false => Spec (CommRingCat.of (NumeratorRing f))
  | true => Spec (CommRingCat.of (DenominatorRing g))
@[expose] def embedding : (b : Bool) → chart f g b ⟶ Spec (CommRingCat.of ℚ[X])
  | false => numeratorBase f
  | true => denominatorBase g
instance embedding_open (b : Bool) : IsOpenImmersion (embedding f g b) := by
  cases b <;> dsimp [embedding] <;> infer_instance

/-- The genuine two-localization cover of the entire rational affine source
chart. The coprimality proof supplies coverage of every source prime. -/
@[expose] def cover (h : IsCoprime f g) : (Spec (CommRingCat.of ℚ[X])).OpenCover where
  I₀ := Bool
  X := chart f g
  f := embedding f g
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro p
    have hp : p ∈ (numeratorBase f).opensRange ⊔ (denominatorBase g).opensRange := by
      rw [chart_ranges_cover f g h]
      trivial
    rcases hp with hp | hp
    · obtain ⟨q,hq⟩ := hp
      exact ⟨false,q,hq⟩
    · obtain ⟨q,hq⟩ := hp
      exact ⟨true,q,hq⟩

lemma compatibility_of_pullback {P X Y Z T : Scheme}
    {a : P ⟶ X} {b : P ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z} (h : IsPullback a b i j)
    (F : X ⟶ T) (G : Y ⟶ T) (hab : a ≫ F = b ≫ G) :
    pullback.fst i j ≫ F = pullback.snd i j ≫ G := by
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [←Category.assoc,h.isoPullback_hom_fst,h.isoPullback_hom_snd] using hab

lemma diagonal_compatibility {X Z T : Scheme} (i : X ⟶ Z) [Mono i] (F : X ⟶ T) :
    pullback.fst i i ≫ F = pullback.snd i i ≫ F := by
  have h : pullback.fst i i = pullback.snd i i := (cancel_mono i).mp pullback.condition
  rw [h]

@[expose] def localMap (h : IsCoprime f g) :
    (b : Bool) → (cover f g h).X b ⟶ ProjectiveJLine318.scheme ℚ
  | false => numeratorMap f g
  | true => denominatorMap f g

lemma compatible (h : IsCoprime f g) (b d : Bool) :
    pullback.fst ((cover f g h).f b) ((cover f g h).f d) ≫ localMap f g h b =
      pullback.snd _ _ ≫ localMap f g h d := by
  cases b <;> cases d
  · exact diagonal_compatibility _ _
  · exact compatibility_of_pullback (actual_pullback f g) _ _ (projection_compatibility f g)
  · exact compatibility_of_pullback (actual_pullback f g).flip _ _
      (projection_compatibility f g).symm
  · exact diagonal_compatibility _ _

/-- Actual scheme morphism from the entire affine line, glued from the
numerator and denominator domains. This is not just a function on field points. -/
@[expose] def map (h : IsCoprime f g) :
    Spec (CommRingCat.of ℚ[X]) ⟶ ProjectiveJLine318.scheme ℚ :=
  (cover f g h).glueMorphisms (localMap f g h) (compatible f g h)

@[reassoc] theorem numerator_restriction (h : IsCoprime f g) :
    numeratorBase f ≫ map f g h = numeratorMap f g :=
  (cover f g h).ι_glueMorphisms _ _ false

@[reassoc] theorem denominator_restriction (h : IsCoprime f g) :
    denominatorBase g ≫ map f g h = denominatorMap f g :=
  (cover f g h).ι_glueMorphisms _ _ true

lemma evaluation_over_Q {A : Type} [CommRing A] [Algebra ℚ A] (z : A) (i : Fin 2) :
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) z).toRingHom) ≫
      JLineAtlas318.chart ℚ i) ≫ ProjectiveJLine318.structureMap ℚ =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) := by
  rw [Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (Polynomial.aeval (R:=ℚ) z).commutes r

/-- The glued morphism retains the same rational coefficient map globally. -/
@[reassoc] theorem over_Q (h : IsCoprime f g) :
    map f g h ≫ ProjectiveJLine318.structureMap ℚ =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])) := by
  apply (cover f g h).hom_ext
  intro b
  cases b
  · change numeratorBase f ≫ (map f g h ≫ _) = numeratorBase f ≫ _
    rw [←Category.assoc,numerator_restriction]
    change numeratorMap f g ≫ _ = _
    rw [show numeratorMap f g ≫ ProjectiveJLine318.structureMap ℚ =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (NumeratorRing f))) from evaluation_over_Q _ 0]
    unfold numeratorBase
    rw [←Spec.map_comp]
    congr 1
  · change denominatorBase g ≫ (map f g h ≫ _) = denominatorBase g ≫ _
    rw [←Category.assoc,denominator_restriction]
    change denominatorMap f g ≫ _ = _
    rw [show denominatorMap f g ≫ ProjectiveJLine318.structureMap ℚ =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (DenominatorRing g))) from evaluation_over_Q _ 1]
    unfold denominatorBase
    rw [←Spec.map_comp]
    congr 1

end RationalPairGluing318
