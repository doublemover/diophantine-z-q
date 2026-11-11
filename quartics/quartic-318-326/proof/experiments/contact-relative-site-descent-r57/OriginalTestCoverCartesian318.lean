module
public import OriginalTestDoubleIso318
public section
noncomputable section
namespace OriginalTestCoverCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RelativeLineClassBaseChange318
open OriginalTestCechCoordinates318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T T' : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (b' : T' ⟶ B)
  (g : T' ⟶ T) (hg : g ≫ b = b')

/-- The unchanged original totalMap is a genuine base change of the
original test map, proved by its original universal property. -/
lemma cartesian : IsPullback (f q b b' g hg) (p' q b') (p q b) g := by
  apply IsPullback.mk'
  · exact totalMap_snd q b b' g hg
  · intro Z x y hx hy
    apply pullback.hom_ext
    · have h := congrArg (fun a => a ≫ pullback.fst q b) hx
      simpa only [Category.assoc,totalMap_fst] using h
    · exact hy
  · intro Z x y hxy
    have hh : (x ≫ pullback.fst q b) ≫ q = y ≫ b' := by
      calc
        _ = (x ≫ p q b) ≫ b := by
          simpa only [Category.assoc] using congrArg (fun a => x ≫ a)
            (pullback.condition (f:=q) (g:=b))
        _ = (y ≫ g) ≫ b := congrArg (fun a => a ≫ b) hxy
        _ = y ≫ b' := by rw [Category.assoc,hg]
    let z := pullback.lift (x ≫ pullback.fst q b) y hh
    refine ⟨z,?_,pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc,totalMap_fst,z,pullback.lift_fst]
    · simpa only [Category.assoc,totalMap_snd,z,pullback.lift_snd_assoc] using hxy.symm

instance totalMap_affine [IsAffineHom g] : IsAffineHom (f q b b' g hg) :=
  MorphismProperty.of_isPullback (cartesian q b b' g hg).flip (inferInstance : IsAffineHom g)
instance totalMap_flat [Flat g] : Flat (f q b b' g hg) :=
  MorphismProperty.of_isPullback (cartesian q b b' g hg).flip (inferInstance : Flat g)
instance totalMap_surjective [Surjective g] : Surjective (f q b b' g hg) :=
  MorphismProperty.of_isPullback (cartesian q b b' g hg).flip (inferInstance : Surjective g)
end OriginalTestCoverCartesian318
