module
public import InvariantNormalizedFrames318
public import WeierstrassGluing318
import all WeierstrassGluing318
public section
noncomputable section
namespace InvariantChartCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassOverlap318 DifferentialChartMaps318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

section Generic
variable {S : Type u} [CommRing S]
theorem localization_preimage (s : S) (p : Spec (CommRingCat.of S)) (hs : s ∉ p.asIdeal) :
    ∃ q : Spec (CommRingCat.of (Localization.Away s)),
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))) q=p := by
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away s))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
    exact hs
  exact hp

theorem finite_localizations_cover {ι : Type*} (s : ι → S) (hspan : Ideal.span (Set.range s)=⊤)
    (p : Spec (CommRingCat.of S)) :
    ∃ i, ∃ q : Spec (CommRingCat.of (Localization.Away (s i))),
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s i)))) q=p := by
  have hi : ∃ i, s i ∉ p.asIdeal := by
    by_contra h
    push_neg at h
    have hp : Ideal.span (Set.range s) ≤ p.asIdeal := Ideal.span_le.mpr (by
      rintro _ ⟨i,rfl⟩; exact h i)
    rw [hspan] at hp
    exact p.isPrime.ne_top (top_le_iff.mp hp)
  obtain ⟨i,hi⟩ := hi
  obtain ⟨q,hq⟩ := localization_preimage (s i) p hi
  exact ⟨i,q,hq⟩
end Generic

@[expose] def finiteInto (A B : R) (i : Fin 2) :
    Spec (CommRingCat.of (WeierstrassKaehler318.AffineChart A B i)) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom (algebraMap (Affine A B) (WeierstrassKaehler318.AffineChart A B i))) ≫
    WeierstrassGluing318.finiteChart A B
@[expose] def infinityInto (A B : R) :
    Spec (CommRingCat.of (InfinityChart A B)) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom (algebraMap (Infinity A B) (InfinityChart A B))) ≫
    WeierstrassGluing318.infinityChart A B

instance finiteInto_open (A B : R) (i : Fin 2) : IsOpenImmersion (finiteInto A B i) := by
  have h : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Affine A B) (WeierstrassKaehler318.AffineChart A B i)))) :=
    IsOpenImmersion.of_isLocalization (ShortAffineJacobian318.presentation A B i).jacobian
  unfold finiteInto
  infer_instance
instance infinityInto_open (A B : R) : IsOpenImmersion (infinityInto A B) := by
  have h : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Infinity A B) (InfinityChart A B)))) :=
    IsOpenImmersion.of_isLocalization (InfinityChart318.presentation A B).jacobian
  unfold infinityInto
  infer_instance

/-- All three actual normalized invariant differential charts cover the genuine glued curve. -/
theorem charts_cover (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2)))
    (p : WeierstrassGluing318.scheme A B) :
    (∃ i, ∃ q, finiteInto A B i q=p) ∨ (∃ q, infinityInto A B q=p) := by
  have hf (a : ShortAffineScheme318.scheme A B) : ∃ i, ∃ q,
      finiteInto A B i q=WeierstrassGluing318.finiteChart A B a := by
    obtain ⟨i,q,hq⟩ := finite_localizations_cover
      (fun i : Fin 2 => (ShortAffineJacobian318.presentation A B i).jacobian)
      (ShortAffineJacobian318.jacobian_span A B hD) a
    exact ⟨i,q,congrArg (WeierstrassGluing318.finiteChart A B) hq⟩
  rcases WeierstrassGluing318.charts_cover A B p with ⟨a,rfl⟩|⟨b,rfl⟩
  · exact Or.inl (hf a)
  · by_cases hz : InfinityChart318.z A B ∈ b.asIdeal
    · have hj : (InfinityChart318.presentation A B).jacobian ∉ b.asIdeal := by
        intro hj
        have hp : Ideal.span ({InfinityChart318.z A B,(InfinityChart318.presentation A B).jacobian} :
            Set (Infinity A B)) ≤ b.asIdeal := Ideal.span_le.mpr (by
          intro t ht
          rcases Set.mem_insert_iff.mp ht with rfl|ht
          · exact hz
          · exact Set.mem_singleton_iff.mp ht ▸ hj)
        rw [InfinitySmooth318.cover_span] at hp
        exact b.isPrime.ne_top (top_le_iff.mp hp)
      obtain ⟨q,hq⟩ := localization_preimage (InfinityChart318.presentation A B).jacobian b hj
      exact Or.inr ⟨q,congrArg (WeierstrassGluing318.infinityChart A B) hq⟩
    · obtain ⟨q,hq⟩ := localization_preimage (S:=Infinity A B) (InfinityChart318.z A B) b hz
      obtain ⟨i,a,ha⟩ := hf (WeierstrassGluing318.intoAffine A B q)
      apply Or.inl
      refine ⟨i,a,ha.trans ?_⟩
      have hglue := congrArg (fun f : WeierstrassGluing318.overlap A B ⟶ WeierstrassGluing318.scheme A B => f q)
        (pushout.condition (f:=WeierstrassGluing318.intoAffine A B) (g:=WeierstrassGluing318.intoInfinity A B))
      have hq' : WeierstrassGluing318.intoInfinity A B q=b := by
        exact hq
      have hi : (WeierstrassGluing318.intoInfinity A B ≫
          pushout.inr (WeierstrassGluing318.intoAffine A B) (WeierstrassGluing318.intoInfinity A B)) q =
            WeierstrassGluing318.infinityChart A B b := by
        rw [Scheme.Hom.comp_apply,hq']
        rfl
      exact hglue.trans hi
end InvariantChartCover318
