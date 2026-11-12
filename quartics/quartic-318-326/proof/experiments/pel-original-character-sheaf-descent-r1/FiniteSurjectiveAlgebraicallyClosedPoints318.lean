module
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public section
noncomputable section
namespace FiniteSurjectiveAlgebraicallyClosedPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]

/-- A genuine field-valued point lifts through a finite surjective
morphism over an algebraically closed field. The proof uses a closed
point of the ACTUAL fiber and its residue-field isomorphism, not a
choice of an arbitrary underlying source prime. -/
theorem exists_lift (y : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = y := by
  let F := pullback f y
  let g : F ⟶ Spec (CommRingCat.of K) := pullback.snd f y
  letI : IsFinite g := inferInstanceAs (IsFinite (pullback.snd f y))
  letI : Surjective g := inferInstanceAs (Surjective (pullback.snd f y))
  letI : JacobsonSpace F := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨a,ha⟩ := g.surjective (IsLocalRing.closedPoint K)
  have hn : (Set.univ : Set F).Nonempty := ⟨a,Set.mem_univ a⟩
  obtain ⟨b,hb⟩ := nonempty_inter_closedPoints hn isClosed_univ.isLocallyClosed
  let s : Spec (CommRingCat.of K) ⟶ F := pointOfClosedPoint g b hb.2
  have hs : s ≫ g = 𝟙 _ := pointOfClosedPoint_comp g b hb.2
  refine ⟨s ≫ pullback.fst f y, ?_⟩
  calc
    (s ≫ pullback.fst f y) ≫ f = s ≫ (pullback.snd f y ≫ y) := by
      rw [Category.assoc,pullback.condition]
    _ = y := by rw [←Category.assoc,hs,Category.id_comp]

/-- The lift preserves the specified field structure whenever the
original morphism does. No automorphism of the base field is inserted. -/
theorem exists_lift_over (sX : X ⟶ Spec (CommRingCat.of K))
    (sY : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ sY = sX)
    (y : Spec (CommRingCat.of K) ⟶ Y) (hy : y ≫ sY = 𝟙 _) :
    ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = y ∧ x ≫ sX = 𝟙 _ := by
  obtain ⟨x,hx⟩ := exists_lift f y
  exact ⟨x,hx,by rw [←hf,←Category.assoc,hx,hy]⟩
end FiniteSurjectiveAlgebraicallyClosedPoints318
