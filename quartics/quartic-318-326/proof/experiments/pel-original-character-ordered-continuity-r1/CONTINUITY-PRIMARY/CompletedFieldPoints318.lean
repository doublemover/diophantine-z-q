module
public import CubicClosedImmersion318
public import LiteralWeierstrassPoints318
import all WeierstrassGluing318
public section
noncomputable section
namespace CompletedFieldPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassOverlap318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

@[expose] def SchemePoints (A B : R) :=
  {f : Spec (CommRingCat.of K) ⟶ WeierstrassGluing318.scheme A B //
    f ≫ WeierstrassGluing318.structureMap A B=Spec.map (CommRingCat.ofHom (algebraMap R K))}

@[expose] def finiteInclusion (A B : R) (p : AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    SchemePoints (K:=K) A B := ⟨p.val ≫ WeierstrassGluing318.finiteChart A B,by
      rw [Category.assoc,WeierstrassGluing318.finiteChart_structure]
      exact p.property⟩
@[expose] def infinityPoint (A B : R) : SchemePoints (K:=K) A B :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ WeierstrassGluing318.infinity A B,by
    rw [Category.assoc,WeierstrassGluing318.infinity_section,Category.comp_id]⟩

lemma finiteInclusion_injective (A B : R) : Function.Injective (finiteInclusion (K:=K) A B) := by
  intro p q h
  apply Subtype.ext
  exact (cancel_mono (WeierstrassGluing318.finiteChart A B)).mp (congrArg Subtype.val h)

/-- A genuine field-valued point factors through one of the two actual open charts. -/
lemma field_chart_cases (A B : R) (f : Spec (CommRingCat.of K) ⟶ WeierstrassGluing318.scheme A B) :
    (∃ a, a ≫ WeierstrassGluing318.finiteChart A B=f) ∨
      (∃ b, b ≫ WeierstrassGluing318.infinityChart A B=f) := by
  rcases WeierstrassGluing318.charts_cover A B (f default) with ha | hb
  · left
    have h : Set.range f ⊆ Set.range (WeierstrassGluing318.finiteChart A B) := by
      rintro _ ⟨p,rfl⟩
      obtain ⟨a,ha⟩ := ha
      exact ⟨a,ha.trans (congrArg f (Subsingleton.elim default p))⟩
    exact ⟨IsOpenImmersion.lift _ f h,IsOpenImmersion.lift_fac _ _ h⟩
  · right
    have h : Set.range f ⊆ Set.range (WeierstrassGluing318.infinityChart A B) := by
      rintro _ ⟨p,rfl⟩
      obtain ⟨b,hb⟩ := hb
      exact ⟨b,hb.trans (congrArg f (Subsingleton.elim default p))⟩
    exact ⟨IsOpenImmersion.lift _ f h,IsOpenImmersion.lift_fac _ _ h⟩

lemma infinity_hom_zero (A B : R) (φ : Infinity A B →ₐ[R] K) (hz : φ (InfinityChart318.z A B)=0) :
    φ=(Algebra.ofId R K).comp (InfinityChart318.origin A B) := by
  have he := congrArg φ (InfinityChart318.relation A B)
  have hx : φ (InfinityChart318.x A B)=0 := by
    simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,hz] at he
    simpa using he
  apply InfinityChart318.hom_ext
  · simpa using hx
  · simpa using hz

/-- Every completed field-valued point is finite or the actual infinity section. -/
theorem finite_or_infinity (A B : R) (p : SchemePoints (K:=K) A B) :
    (∃ a,finiteInclusion A B a=p) ∨ p=infinityPoint A B := by
  rcases field_chart_cases A B p.val with ⟨a,ha⟩ | ⟨b,hb⟩
  · left
    have hab : a ≫ ShortAffineScheme318.structureMap A B=Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [←WeierstrassGluing318.finiteChart_structure,←Category.assoc,ha]
      exact p.property
    exact ⟨⟨a,hab⟩,Subtype.ext ha⟩
  · have hbb : b ≫ InfinitySmooth318.structureMap A B=Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [←WeierstrassGluing318.infinityChart_structure,←Category.assoc,hb]
      exact p.property
    let φ : Infinity A B →ₐ[R] K := Spec.homEquivAlgHom ⟨b,hbb⟩
    have hbφ : Spec.map (CommRingCat.ofHom φ.toRingHom)=b := by
      exact congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨b,hbb⟩)
    by_cases hz : φ (InfinityChart318.z A B)=0
    · right
      apply Subtype.ext
      rw [←hb,←hbφ,infinity_hom_zero A B φ hz]
      change Spec.map (CommRingCat.ofHom ((algebraMap R K).comp (InfinityChart318.origin A B).toRingHom)) ≫
        WeierstrassGluing318.infinityChart A B=_
      rw [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
      rfl
    · left
      let ψ : InfinityOverlap A B →ₐ[R] K :=
        IsLocalization.Away.liftAlgHom (f := φ) (InfinityChart318.z A B) (isUnit_iff_ne_zero.mpr hz)
      have hψ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ WeierstrassGluing318.intoInfinity A B=b := by
        unfold WeierstrassGluing318.intoInfinity
        rw [←Spec.map_comp,←hbφ]
        congr 1
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        exact IsLocalization.Away.lift_eq _ (isUnit_iff_ne_zero.mpr hz) x
      let a := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ WeierstrassGluing318.intoAffine A B
      have ha : a ≫ WeierstrassGluing318.finiteChart A B=p.val := by
        dsimp only [a]
        rw [Category.assoc]
        change _ ≫ (WeierstrassGluing318.intoAffine A B ≫ pushout.inl _ _)=_
        rw [pushout.condition,←Category.assoc,hψ]
        exact hb
      have hab : a ≫ ShortAffineScheme318.structureMap A B=Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
        rw [←WeierstrassGluing318.finiteChart_structure,←Category.assoc,ha]
        exact p.property
      exact ⟨⟨a,hab⟩,Subtype.ext ha⟩

/-- The actual infinity point has empty inverse image in the finite affine chart. -/
lemma infinity_preimage_finite (A B : R) :
    (infinityPoint (K:=K) A B).val ⁻¹ᵁ (WeierstrassGluing318.finiteChart A B).opensRange=⊥ := by
  rw [←CubicChartGeometry318.embedding_preimage_Z]
  rw [←Scheme.Hom.comp_preimage]
  change (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
    InfinitySmooth318.infinity A B ≫ WeierstrassGluing318.infinityChart A B ≫
      CubicProjectiveMap318.embedding A B) ⁻¹ᵁ _=⊥
  rw [CubicProjectiveMap318.infinity_embedding,Scheme.Hom.comp_preimage,Scheme.Hom.comp_preimage,
    CubicChartGeometry318.infinityMap_preimage _ _ _ (MvPolynomial.isHomogeneous_X R 2) (by omega)]
  simp only [CubicChartGeometry318.infinityCoordinates,MvPolynomial.aeval_X,Matrix.cons_val_two]
  unfold InfinitySmooth318.infinity
  rw [SpecMap_preimage_basicOpen]
  change Spec.map (CommRingCat.ofHom (algebraMap R K)) ⁻¹ᵁ
    PrimeSpectrum.basicOpen ((InfinityChart318.origin A B) (InfinityChart318.z A B))=⊥
  rw [InfinityChart318.origin_z]
  simp only [PrimeSpectrum.basicOpen_zero]
  rfl

lemma finite_ne_infinity (A B : R) (p : AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    finiteInclusion A B p ≠ infinityPoint A B := by
  intro h
  have hp : (default : Spec (CommRingCat.of K)) ∈
      (infinityPoint (K:=K) A B).val ⁻¹ᵁ (WeierstrassGluing318.finiteChart A B).opensRange := by
    rw [←h]
    exact ⟨p.val default,rfl⟩
  rw [infinity_preimage_finite] at hp
  exact hp

@[expose] def fromOption (A B : R) : Option (AffineSchemeSolutions318.SchemePoints (K:=K) A B) →
    SchemePoints (K:=K) A B
  | none => infinityPoint A B
  | some p => finiteInclusion A B p

lemma fromOption_bijective (A B : R) : Function.Bijective (fromOption (K:=K) A B) := by
  constructor
  · intro p q h
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some q => exact (finite_ne_infinity A B q h.symm).elim
    | some p =>
      cases q with
      | none => exact (finite_ne_infinity A B p h).elim
      | some q => exact congrArg some (finiteInclusion_injective A B h)
  · intro p
    rcases finite_or_infinity A B p with ⟨a,ha⟩ | h
    · exact ⟨some a,ha⟩
    · exact ⟨none,h.symm⟩

/-- Actual completed Scheme field-points are exactly finite Scheme points plus one infinity point. -/
@[expose] def completedEquiv (A B : R) : SchemePoints (K:=K) A B ≃
    Option (AffineSchemeSolutions318.SchemePoints (K:=K) A B) :=
  (Equiv.ofBijective (fromOption A B) (fromOption_bijective A B)).symm

@[simp] theorem completedEquiv_infinity (A B : R) : completedEquiv (K:=K) A B (infinityPoint A B)=none :=
  (completedEquiv A B).apply_symm_apply none
@[simp] theorem completedEquiv_finite (A B : R) (p : AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    completedEquiv A B (finiteInclusion A B p)=some p :=
  (completedEquiv A B).apply_symm_apply (some p)

end CompletedFieldPoints318
