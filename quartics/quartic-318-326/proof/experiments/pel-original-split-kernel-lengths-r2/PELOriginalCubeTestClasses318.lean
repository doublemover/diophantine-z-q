module
public import PELOriginalPolarizationCubeIdentity318
public import PELOriginalRelativePolarizationTransformation318
public import PELOriginalSchemePointGroup318
public section
noncomputable section
namespace PELOriginalCubeTestClasses318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalProductChartCover318 PELOriginalTripleProductReduced318 PELOriginalTripleComplexPoints318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemeGroupAssociativity318
open PELOriginalSchemePointGroup318
variable (τ : ℂ) (hτ : 0 < τ.im)
variable {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
@[expose] def value (f : Points τ hτ Y ρ) : Class Y :=
  LineClassPullbackHom318.pullback f.val (classOf (line τ hτ))
@[expose] def tripleLift (f g k : Points τ hτ Y ρ) : Y ⟶ Triple τ hτ :=
  pullback.lift (pullback.lift f.val g.val (f.property.trans g.property.symm)) k.val
    (by rw [baseMap,←Category.assoc,pullback.lift_fst,f.property,k.property])
lemma first_lift (f g k : Points τ hτ Y ρ) : tripleLift τ hτ ρ f g k≫first τ hτ=f.val := by
  simp only [tripleLift,first,←Category.assoc,pullback.lift_fst]
lemma second_lift (f g k : Points τ hτ Y ρ) : tripleLift τ hτ ρ f g k≫second τ hτ=g.val := by
  simp only [tripleLift,second,←Category.assoc,pullback.lift_fst,pullback.lift_snd]
lemma third_lift (f g k : Points τ hτ Y ρ) : tripleLift τ hτ ρ f g k≫third τ hτ=k.val :=
  pullback.lift_snd _ _ _
lemma structure_lift (f g k : Points τ hτ Y ρ) : tripleLift τ hτ ρ f g k≫structureMap τ hτ=ρ := by
  rw [←first_over,←Category.assoc,first_lift,f.property]
lemma firstTwo_lift (f g k : Points τ hτ Y ρ) : tripleLift τ hτ ρ f g k≫firstTwo τ hτ=(f+g).val := by
  rw [firstTwo,combine_naturality τ hτ _ _ _ _
    (by rw [first_lift,second_lift,f.property,g.property]),first_lift,second_lift]
  rfl
lemma firstThird_lift (f g k : Points τ hτ Y ρ) :
    tripleLift τ hτ ρ f g k≫PELOriginalCubeSchemeMaps318.firstThird τ hτ=(f+k).val := by
  rw [PELOriginalCubeSchemeMaps318.firstThird,combine_naturality τ hτ _ _ _ _
    (by rw [first_lift,third_lift,f.property,k.property]),first_lift,third_lift]
  rfl
lemma lastTwo_lift (f g k : Points τ hτ Y ρ) : tripleLift τ hτ ρ f g k≫lastTwo τ hτ=(g+k).val := by
  rw [lastTwo,combine_naturality τ hτ _ _ _ _
    (by rw [second_lift,third_lift,g.property,k.property]),second_lift,third_lift]
  rfl
lemma sum_lift (f g k : Points τ hτ Y ρ) : tripleLift τ hτ ρ f g k≫leftAssociated τ hτ=((f+g)+k).val := by
  rw [leftAssociated,combine_naturality τ hτ _ _ _ _
    (by rw [firstTwo_lift,third_lift,(f+g).property,k.property]),firstTwo_lift,third_lift]
  rfl
lemma zero_lift (f g k : Points τ hτ Y ρ) :
    tripleLift τ hτ ρ f g k≫PELOriginalCubeSchemeMaps318.zeroMap τ hτ=(0 : Points τ hτ Y ρ).val := by
  rw [PELOriginalCubeSchemeMaps318.zeroMap,←Category.assoc,structure_lift]
  rfl
lemma class_composition {Z W : Scheme} (f : Y ⟶ Z) (g : Z ⟶ W) (c : Class W) :
    LineClassPullbackHom318.pullback f (LineClassPullbackGroup318.hom g c)=
      LineClassPullbackHom318.pullback (f≫g) c :=
  (LineClassPullbackLaws318.pullback_composition f g c).symm

/-- The actual universal cube identity on ANY test scheme, with no
reducedness or finite-type assumption on that test. -/
theorem cube (f g k : Points τ hτ Y ρ) :
    value τ hτ ρ ((f+g)+k)*value τ hτ ρ f*value τ hτ ρ g*value τ hτ ρ k=
      value τ hτ ρ (f+g)*value τ hτ ρ (f+k)*value τ hτ ρ (g+k)*value τ hτ ρ 0 := by
  have h := congrArg (LineClassPullbackHom318.pullback (tripleLift τ hτ ρ f g k))
    (PELOriginalPolarizationCubeIdentity318.class_formula τ hτ)
  simp only [PELOriginalPolarizationCubeIdentity318.expression,map_mul,
    PELOriginalPolarizationCubeIdentity318.pull,class_composition,
    PELOriginalCubeLineFrames318.positions,PELOriginalCubeSchemeMaps318.maps,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Bool.false_eq_true,if_false,if_true,
    sum_lift,first_lift,second_lift,third_lift,firstTwo_lift,firstThird_lift,lastTwo_lift,zero_lift] at h
  exact h
end PELOriginalCubeTestClasses318
