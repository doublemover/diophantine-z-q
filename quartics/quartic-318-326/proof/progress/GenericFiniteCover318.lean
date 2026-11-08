module
public import FinitePairSchemeCover318
public section
noncomputable section
namespace GenericFiniteCover318
open AlgebraicGeometry CategoryTheory
universe u v
variable {R T S : Type u} [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S]
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

@[expose] def lift (f : T →ₐ[R] S) (a : T) :
    Localization.Away a →ₐ[R] Localization.Away (f a) :=
  IsLocalization.Away.liftAlgHom (f := (IsScalarTower.toAlgHom R S _).comp f) a
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f a)) (f a))

theorem lift_on_base (f : T →ₐ[R] S) (a x : T) :
    lift f a (algebraMap T (Localization.Away a) x) =
      algebraMap S (Localization.Away (f a)) (f x) := by
  simp only [lift, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
  rfl

/-- A complete localization-cover comparison, proved before any large coordinate
ring or concrete addition law is substituted. -/
theorem comparison {ι : Type v} (f : T →ₐ[R] S) (a : ι → T)
    (ha : Ideal.span (Set.range a) = ⊤) (Z : Scheme.{u})
    (g : Spec (CommRingCat.of T) ⟶ Z) (h : Spec (CommRingCat.of S) ⟶ Z)
    (localLaw : ∀ i, Spec (CommRingCat.of (Localization.Away (a i))) ⟶ Z)
    (restriction : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap T (Localization.Away (a i)))) ≫ g = localLaw i)
    (agreement : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f (a i))))) ≫ h =
      Spec.map (CommRingCat.ofHom (lift f (a i)).toRingHom) ≫ localLaw i) :
    h = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g := by
  have he : Ideal.span (Set.range (fun i => f (a i))) = ⊤ := by
    have h := congrArg (Ideal.map f.toRingHom) ha
    rw [Ideal.map_span, Ideal.map_top] at h
    rw [Set.range_comp']
    change Ideal.span (f.toRingHom '' Set.range a) = ⊤
    exact h
  let cover := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S)
    (fun i => f (a i)) he).openCover
  apply cover.hom_ext
  intro i
  change Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f (a i))))) ≫ h =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f (a i))))) ≫
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g)
  rw [agreement i, ← restriction i, ← Category.assoc, ← Spec.map_comp]
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact lift_on_base f (a i) x
end GenericFiniteCover318
