module
public import SelectedGeneralizedInstallOriginOpen318
public import SelectedGeneralizedInfinityActualJets318
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedInfinityCartier318
open SelectedGeneralizedInfinityActualJets318 SelectedGeneralizedGluedCarrier318
open SelectedGeneralizedInstallOriginOpen318

namespace SelectedGeneralizedGeometricIdentityJets318

universe u
variable {R V V' : Type u} [CommRing R]
variable [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
variable [AddCommGroup V'] [Module R V'] [Module Rᵐᵒᵖ V'] [IsCentralScalar R V']
local notation "B" => TrivSqZeroExt R V
local notation "B'" => TrivSqZeroExt R V'
local notation "S" => Spec (CommRingCat.of B)
local notation "S'" => Spec (CommRingCat.of B')
local notation "fst" => TrivSqZeroExt.fstHom R R V

@[expose] def augScheme (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]
    [Module Rᵐᵒᵖ V] [IsCentralScalar R V] :
    Base R ⟶ Spec (CommRingCat.of (TrivSqZeroExt R V)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom)

@[expose] def jetMap (l : V →ₗ[R] V') : S' ⟶ S :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)

theorem point_reduces (d : Rˣ) (v : V) : fst.comp (point d v) = augmentation d := by
  apply IsLocalization.algHom_ext (Submonoid.powers (den d))
  apply AlgHom.ext
  intro a
  change fst (point d v (algebraMap (Chart d) (OpenRing d) a)) =
    augmentation d (algebraMap (Chart d) (OpenRing d) a)
  rw [point_map,augmentation_map]
  exact congrArg (fun f : Chart d →ₐ[R] R => f a) (raw_augmentation d v)

/-- Each algebraic local point is now an actual map to the same
whole generalized two-chart carrier. -/
@[expose] def geomJet (d : Rˣ) (v : V) : S ⟶ Carrier d :=
  Spec.map (CommRingCat.ofHom (point d v).toRingHom) ≫ install d

theorem geomJet_over (d : Rˣ) (v : V) :
    geomJet d v ≫ overBase d = Spec.algebraMap R B := by
  rw [geomJet,Category.assoc,install_over]
  unfold Spec.algebraMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (point d v).commutes

theorem geomJet_reduces (d : Rˣ) (v : V) :
    augScheme R V ≫ geomJet d v = identitySection d := by
  unfold augScheme geomJet
  rw [← Category.assoc,← Spec.map_comp]
  have h := congrArg AlgHom.toRingHom (point_reduces d v)
  change Spec.map (CommRingCat.ofHom ((fst.comp (point d v)).toRingHom)) ≫ install d = _
  rw [h]
  exact originLift_install d

theorem geomJet_natural (d : Rˣ) (l : V →ₗ[R] V') (v : V) :
    jetMap l ≫ geomJet d v = geomJet d (l v) := by
  have h : (TrivSqZeroExt.map l).comp (point d v) = point d (l v) := by
    apply ext_local d
    · rw [AlgHom.comp_apply,point_parameter,point_parameter,TrivSqZeroExt.map_inr]
    · rw [AlgHom.comp_apply,point_ordinate,point_ordinate,map_zero]
  unfold jetMap geomJet
  rw [← Category.assoc,← Spec.map_comp]
  exact congrArg (fun f : OpenRing d →ₐ[R] B' =>
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ install d) h

theorem geomJet_injective (d : Rˣ) : Function.Injective (geomJet d (V := V)) := by
  intro v w h
  have hh : Spec.map (CommRingCat.ofHom (point d v).toRingHom) =
      Spec.map (CommRingCat.ofHom (point d w).toRingHom) := (cancel_mono (install d)).1 h
  have hh' := Spec.map_injective hh
  have heq := congrArg (fun f : CommRingCat.of (OpenRing d) ⟶ CommRingCat.of B =>
    f.hom (localT d)) hh'
  change point d v (localT d) = point d w (localT d) at heq
  rw [point_parameter,point_parameter] at heq
  exact TrivSqZeroExt.inr_injective heq

theorem aug_surjective : Function.Surjective (augScheme R V) := by
  let f : B →+* R := fst.toRingHom
  have hs : Function.Surjective f := fun r => ⟨TrivSqZeroExt.inl r,rfl⟩
  intro x
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker f : Set B) := by
    change (RingHom.ker f : Set B) ⊆ (x.asIdeal : Set B)
    intro a ha
    have h0 : a.fst = 0 := RingHom.mem_ker.mp ha
    have h : a = TrivSqZeroExt.inr a.snd := TrivSqZeroExt.ext h0 rfl
    refine x.2.mem_of_pow_mem 2 ?_
    rw [h,pow_two,TrivSqZeroExt.inr_mul_inr]
    exact x.asIdeal.zero_mem
  rw [← _root_.range_comap_of_surjective R f hs] at hx
  obtain ⟨a,ha⟩ := hx
  refine ⟨a,?_⟩
  change PrimeSpectrum.comap f a = x
  exact ha

/-- Classification of all actual split first-order maps to this same
generalized carrier which reduce to the true identity. -/
theorem exists_geomJet (d : Rˣ) (p : S ⟶ Carrier d)
    (hb : p ≫ overBase d = Spec.algebraMap R B)
    (he : augScheme R V ≫ p = identitySection d) :
    ∃ v : V, p = geomJet d v := by
  have hr : Set.range p ⊆ Set.range (install d) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨a,ha⟩ := (aug_surjective (R := R) (V := V)) x
    refine ⟨originLift d a,?_⟩
    have h := congrArg (fun F : Base R ⟶ Carrier d => F a) he
    rw [Scheme.Hom.comp_apply,ha,← originLift_install d,Scheme.Hom.comp_apply] at h
    exact h.symm
  let q := IsOpenImmersion.lift (install d) p hr
  have hq : q ≫ install d = p := IsOpenImmersion.lift_fac _ _ _
  have hqb : q ≫ Spec.algebraMap R (OpenRing d) = Spec.algebraMap R B := by
    rw [← install_over d,← Category.assoc,hq,hb]
  let b : OpenRing d →ₐ[R] B := Spec.homEquivAlgHom ⟨q,hqb⟩
  have heval : Spec.map (CommRingCat.ofHom b.toRingHom) = q :=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨q,hqb⟩)
  have hgeom : Spec.map (CommRingCat.ofHom b.toRingHom) ≫ install d = p := by
    rw [heval,hq]
  have hred : fst.comp b = augmentation d := by
    apply AlgHom.toRingHom_injective
    have H : Spec.map (CommRingCat.ofHom ((fst.comp b).toRingHom)) =
        Spec.map (CommRingCat.ofHom (augmentation d).toRingHom) := by
      apply (cancel_mono (install d)).1
      change Spec.map (CommRingCat.ofHom b.toRingHom ≫ CommRingCat.ofHom fst.toRingHom) ≫
        install d = originLift d ≫ install d
      rw [Spec.map_comp,Category.assoc,hgeom,originLift_install]
      exact he
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective H)
  obtain ⟨v,hv,_⟩ := exact_chart_point d b hred
  exact ⟨v,hgeom.symm.trans (by rw [hv] <;> rfl)⟩

end SelectedGeneralizedGeometricIdentityJets318

#print axioms SelectedGeneralizedGeometricIdentityJets318.exists_geomJet
#print axioms SelectedGeneralizedGeometricIdentityJets318.geomJet_natural
