module
public import AlgebraicFiniteTypeClearDenominator318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace AlgebraicFiniteTypeFiniteOpen318
open AlgebraicGeometry CategoryTheory
variable (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- The finite-open ring map is the literal localization of the
original scalar map, not an abstract isomorphic finite algebra. -/
abbrev localizedMap (r : R) := Localization.awayMap (algebraMap R A) r
lemma localizedMap_source (r a : R) :
    localizedMap R A r (algebraMap R (Localization.Away r) a) =
      algebraMap A (Localization.Away (algebraMap R A r)) (algebraMap R A a) := by
  simp only [localizedMap,Localization.awayMap,IsLocalization.Away.map,IsLocalization.map_eq]

/-- Genuine finite type plus actual algebraicity yields one NONZERO
base denominator and a finite map over that full base open. -/
theorem exists_finite_open [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    ∃ r : R, r ≠ 0 ∧ (localizedMap R A r).Finite := by
  obtain ⟨s,r,hr,hs,hi⟩ := AlgebraicFiniteTypeClearDenominator318.generators R A
  refine ⟨r,hr,?_⟩
  let B := Localization.Away r
  let L := Localization.Away (algebraMap R A r)
  let f : B →+* L := localizedMap R A r
  letI : Algebra R L := ((algebraMap A L).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra B L := f.toAlgebra
  letI : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (localizedMap_source R A r a).symm)
  letI : Algebra.IsIntegral B L :=
    AlgebraicFiniteTypeClearDenominator318.whole_localization_integral R A r B L s hs hi
  have hf : f.FiniteType := RingHom.localization_away_map_finiteType
    R A B L (algebraMap R A) r (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact RingHom.IsIntegral.to_finite
    (show f.IsIntegral from fun z => Algebra.IsIntegral.isIntegral z) hf

/-- Transport the base open along a specified ring equivalence. The
localized scalar map remains literally the original map composed with
that equivalence; the polynomial denominator is proved nonzero. -/
theorem exists_finite_open_of_equiv [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A]
    (P : Type) [CommRing P] (e : P ≃+* R) :
    ∃ p : P, p ≠ 0 ∧
      (Localization.awayMap ((algebraMap R A).comp e.toRingHom) p).Finite := by
  obtain ⟨r,hr,hf⟩ := exists_finite_open R A
  obtain ⟨p,rfl⟩ := e.surjective r
  refine ⟨p,fun hp => hr (hp ▸ e.map_zero),?_⟩
  let g : Localization.Away p ≃+* Localization.Away (e p) :=
    IsLocalization.ringEquivOfRingEquiv _ _ e (Submonoid.map_powers e p)
  have hcomp : (localizedMap R A (e p)).comp g.toRingHom =
      Localization.awayMap ((algebraMap R A).comp e.toRingHom) p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers p)
    ext a
    simp only [RingHom.comp_apply,g,IsLocalization.ringEquivOfRingEquiv_eq,
      localizedMap_source,Localization.awayMap,IsLocalization.Away.map,
      IsLocalization.map_eq]
  rw [←hcomp]
  exact hf.comp (RingHom.Finite.of_surjective g.toRingHom g.surjective)

@[expose] def finiteOpenMap (r : R) :
    Spec (CommRingCat.of (Localization.Away (algebraMap R A r))) ⟶
      Spec (CommRingCat.of (Localization.Away r)) :=
  Spec.map (CommRingCat.ofHom (localizedMap R A r))

/-- The produced finite morphism lies in the exact original affine
projection square. Its source is the FULL inverse base localization. -/
@[reassoc] theorem original_square (r : R) :
    finiteOpenMap R A r ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away r))) =
    Spec.map (CommRingCat.ofHom (algebraMap A
      (Localization.Away (algebraMap R A r)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [finiteOpenMap,←Spec.map_comp,←Spec.map_comp]
  congr 1
  ext a
  exact localizedMap_source R A r a

theorem exists_finite_morphism [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    ∃ r : R, r ≠ 0 ∧ IsFinite (finiteOpenMap R A r) := by
  obtain ⟨r,hr,hf⟩ := exists_finite_open R A
  exact ⟨r,hr,(IsFinite.SpecMap_iff _).mpr hf⟩
end AlgebraicFiniteTypeFiniteOpen318
