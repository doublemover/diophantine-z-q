module
public import PELOriginalPolarizationParallelogram318
public import PELOriginalSchemeGroupAssociativity318
public section
noncomputable section
namespace PELOriginalCubeSchemeMaps318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalTripleProductReduced318 PELOriginalTripleComplexPoints318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemeGroupAssociativity318
variable (τ : ℂ) (hτ : 0 < τ.im)
@[expose] def firstThird : Triple τ hτ ⟶ candidate τ hτ :=
  combine τ hτ (first τ hτ) (third τ hτ) ((first_over τ hτ).trans (third_over τ hτ).symm)
@[expose] def zeroMap : Triple τ hτ ⟶ candidate τ hτ := structureMap τ hτ≫zeroPoint τ hτ
@[expose] def subtract (f g : Triple τ hτ ⟶ candidate τ hτ)
    (hf : f≫π τ hτ=structureMap τ hτ) (hg : g≫π τ hτ=structureMap τ hτ) :
    Triple τ hτ ⟶ candidate τ hτ :=
  combine τ hτ f (g≫inverse τ hτ) (by rw [Category.assoc,inverse_over,hf,hg])
lemma subtract_action (f g : Triple τ hτ ⟶ candidate τ hτ)
    (hf : f≫π τ hτ=structureMap τ hτ) (hg : g≫π τ hτ=structureMap τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ Triple τ hτ) (u v : ComplexVectors)
    (hu : p≫f=candidateComplexPoint τ hτ (projection (P τ) u))
    (hv : p≫g=candidateComplexPoint τ hτ (projection (P τ) v)) :
    p≫subtract τ hτ f g hf hg=candidateComplexPoint τ hτ (projection (P τ) (u-v)) := by
  have hn : p≫(g≫inverse τ hτ)=candidateComplexPoint τ hτ (-projection (P τ) v) := by
    rw [←Category.assoc,hv,inverse_action]
  have he := combine_action τ hτ f (g≫inverse τ hτ)
    (by rw [Category.assoc,inverse_over,hf,hg]) p _ _ hu hn
  apply he.trans
  apply congrArg (candidateComplexPoint τ hτ)
  symm
  rw [sub_eq_add_neg,PELOriginalAdditionSchemeMorphism318.projection_add,
    PELOriginalPolarizationSymmetricSquare318.projection_neg]

/-- Literal eleven scheme maps used by the cube and three auxiliary
balancing factors. The zero map is retained, not silently trivialized. -/
@[expose] def maps : Fin 11 → Triple τ hτ ⟶ candidate τ hτ :=
  ![first τ hτ,second τ hτ,third τ hτ,leftAssociated τ hτ,firstTwo τ hτ,
    firstThird τ hτ,lastTwo τ hτ,zeroMap τ hτ,
    subtract τ hτ (first τ hτ) (second τ hτ) (first_over τ hτ) (second_over τ hτ),
    subtract τ hτ (first τ hτ) (third τ hτ) (first_over τ hτ) (third_over τ hτ),
    subtract τ hτ (second τ hτ) (third τ hτ) (second_over τ hτ) (third_over τ hτ)]
@[expose] def argument (x y z : ComplexVectors) : Fin 11 → ComplexVectors :=
  ![x,y,z,x+y+z,x+y,x+z,y+z,0,x-y,x-z,y-z]
lemma over_complex (t : Fin 11) : maps τ hτ t≫π τ hτ=structureMap τ hτ := by
  fin_cases t
  · exact first_over τ hτ
  · exact second_over τ hτ
  · exact third_over τ hτ
  · exact leftAssociated_over τ hτ
  · exact firstTwo_over τ hτ
  · rw [maps,firstThird,combine_over,first_over]
  · exact lastTwo_over τ hτ
  · rw [maps,zeroMap,Category.assoc,zero_over,Category.comp_id]
  · rw [maps,subtract,combine_over,first_over]
  · rw [maps,subtract,combine_over,first_over]
  · rw [maps,subtract,combine_over,second_over]
lemma point_action (t : Fin 11) (x y z : ComplexVectors) :
    triple τ hτ (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)≫maps τ hτ t=
      candidateComplexPoint τ hτ (projection (P τ) (argument x y z t)) := by
  fin_cases t
  · exact first_action τ hτ _ _ _
  · exact second_action τ hτ _ _ _
  · exact third_action τ hτ _ _ _
  · simpa only [maps,argument,Matrix.cons_val_zero,Matrix.cons_val_succ,
      PELOriginalAdditionSchemeMorphism318.projection_add] using leftAssociated_action τ hτ
        (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)
  · simpa only [maps,argument,Matrix.cons_val_zero,Matrix.cons_val_succ,
      PELOriginalAdditionSchemeMorphism318.projection_add] using firstTwo_action τ hτ
        (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)
  · change _≫firstThird τ hτ=_
    simpa only [PELOriginalAdditionSchemeMorphism318.projection_add] using
      combine_action τ hτ (first τ hτ) (third τ hτ) _ _ _ _
        (first_action τ hτ _ _ _) (third_action τ hτ _ _ _)
  · simpa only [maps,argument,Matrix.cons_val_zero,Matrix.cons_val_succ,
      PELOriginalAdditionSchemeMorphism318.projection_add] using lastTwo_action τ hτ
        (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)
  · change _≫(structureMap τ hτ≫zeroPoint τ hτ)=_
    rw [←Category.assoc,triple_over,Category.id_comp]
    change candidateComplexPoint τ hτ 0=candidateComplexPoint τ hτ (projection (P τ) 0)
    rw [map_zero (QuotientAddGroup.mk' (P τ))]
  · exact subtract_action τ hτ _ _ _ _ _ x y (first_action τ hτ _ _ _) (second_action τ hτ _ _ _)
  · exact subtract_action τ hτ _ _ _ _ _ x z (first_action τ hτ _ _ _) (third_action τ hτ _ _ _)
  · exact subtract_action τ hτ _ _ _ _ _ y z (second_action τ hτ _ _ _) (third_action τ hτ _ _ _)
end PELOriginalCubeSchemeMaps318
