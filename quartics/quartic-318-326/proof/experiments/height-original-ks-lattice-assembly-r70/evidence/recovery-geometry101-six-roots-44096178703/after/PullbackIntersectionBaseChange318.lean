module
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace PullbackIntersectionBaseChange318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {A B X X' : Scheme} (f : A ⟶ X) (g : B ⟶ X) (h : X' ⟶ X)

abbrev ChangedIntersection := pullback (pullback.snd f h) (pullback.snd g h)
abbrev ChangedOriginal := pullback (pullback.fst f g ≫ f) h

@[expose] def leftLeg : ChangedIntersection f g h ⟶ A :=
  pullback.fst _ _ ≫ pullback.fst f h
@[expose] def rightLeg : ChangedIntersection f g h ⟶ B :=
  pullback.snd _ _ ≫ pullback.fst g h
@[expose] def baseLeg : ChangedIntersection f g h ⟶ X' :=
  pullback.fst _ _ ≫ pullback.snd f h

theorem legs_agree : leftLeg f g h ≫ f = rightLeg f g h ≫ g := by
  unfold leftLeg rightLeg
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
    Category.assoc, ← pullback.condition, ← Category.assoc]

theorem left_base : leftLeg f g h ≫ f = baseLeg f g h ≫ h := by
  unfold leftLeg baseLeg
  rw [Category.assoc, Category.assoc, pullback.condition]

@[expose] def forward : ChangedIntersection f g h ⟶ ChangedOriginal f g h :=
  pullback.lift
    (pullback.lift (leftLeg f g h) (rightLeg f g h) (legs_agree f g h))
    (baseLeg f g h) (by
      simpa only [← Category.assoc, pullback.lift_fst] using (left_base f g h))

@[expose] def backLeft : ChangedOriginal f g h ⟶ pullback f h :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f g) (pullback.snd _ _)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := pullback.fst f g ≫ f) (g := h)))

@[expose] def backRight : ChangedOriginal f g h ⟶ pullback g h :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd f g) (pullback.snd _ _)
    (by
      calc
        (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.snd f g) ≫ g =
            pullback.fst (pullback.fst f g ≫ f) h ≫ (pullback.snd f g ≫ g) :=
          Category.assoc _ _ _
        _ = pullback.fst (pullback.fst f g ≫ f) h ≫ (pullback.fst f g ≫ f) :=
          congrArg (fun k : pullback f g ⟶ X =>
            pullback.fst (pullback.fst f g ≫ f) h ≫ k)
            (pullback.condition (f := f) (g := g)).symm
        _ = pullback.snd (pullback.fst f g ≫ f) h ≫ h :=
          pullback.condition)

@[expose] def backward : ChangedOriginal f g h ⟶ ChangedIntersection f g h :=
  pullback.lift (backLeft f g h) (backRight f g h)
    (by simp only [backLeft, backRight, pullback.lift_snd])

/-- The actual intersection of two base-changed charts is the base change
of their actual categorical intersection. No set-theoretic surrogate or
assumption about a target-chart preimage is used. -/
@[expose] def iso : ChangedIntersection f g h ≅ ChangedOriginal f g h where
  hom := forward f g h
  inv := backward f g h
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [forward, backward, backLeft, backRight, leftLeg, rightLeg, baseLeg,
          Category.assoc, pullback.condition]
    · apply pullback.hom_ext <;>
        simp [forward, backward, backLeft, backRight, leftLeg, rightLeg, baseLeg,
          Category.assoc, pullback.condition]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [forward, backward, backLeft, backRight, leftLeg, rightLeg, baseLeg,
          Category.assoc]
    · simp [forward, backward, backLeft, baseLeg, Category.assoc]

end PullbackIntersectionBaseChange318
