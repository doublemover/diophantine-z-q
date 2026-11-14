module
public import PELOriginalRosatiRegularCoefficients318
public import PELOriginalNormalizedPolarizationFamily318
public import PELOriginalUniversalOrderAction318
public section
noncomputable section
namespace PELOriginalRosatiProductMaps318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELPrincipalOrderCoordinates318 PELOriginalComplementaryOrder318 PELOriginalComplementaryHermitian318
open PELOriginalOrderHermitianAdjoint318 PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318 PELOriginalSchemePointGroup318
open PELOriginalSchemeAdditionOperations318 PELOriginalNormalizedPolarizationFamily318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
abbrev action := PELOriginalUniversalOrderAction318.endomorphism τ hτ (baseMap τ hτ)
@[expose] def points : Fin 9 → Points τ hτ (Product τ hτ) (baseMap τ hτ) :=
  ![firstPoint τ hτ,secondPoint τ hτ,action τ hτ a (firstPoint τ hτ),
    action τ hτ (adjoint a) (secondPoint τ hτ),
    action τ hτ a (firstPoint τ hτ)+secondPoint τ hτ,
    firstPoint τ hτ+action τ hτ (adjoint a) (secondPoint τ hτ),
    action τ hτ a (firstPoint τ hτ)-secondPoint τ hτ,
    action τ hτ (complement a) (firstPoint τ hτ),
    action τ hτ (complement (adjoint a)) (secondPoint τ hτ)]
@[expose] def maps (t : Fin 9) : Product τ hτ⟶candidate τ hτ := (points τ hτ a t).val
lemma over_complex (t : Fin 9) : maps τ hτ a t≫π τ hτ=baseMap τ hτ := (points τ hτ a t).property
@[expose] def argument (z w : ComplexVectors) : Fin 9 → ComplexVectors :=
  ![z,w,linear a z,linear (adjoint a) w,linear a z+w,z+linear (adjoint a) w,
    linear a z-w,linear (complement a) z,linear (complement (adjoint a)) w]
lemma point_action (t : Fin 9) (z w : ComplexVectors) :
    pair τ hτ (projection (P τ) z) (projection (P τ) w)≫maps τ hτ a t=
      candidateComplexPoint τ hτ (projection (P τ) (argument a z w t)) := by
  let p := pair τ hτ (projection (P τ) z) (projection (P τ) w)
  have hx : p≫(firstPoint τ hτ).val=candidateComplexPoint τ hτ (projection (P τ) z) := pair_fst τ hτ _ _
  have hy : p≫(secondPoint τ hτ).val=candidateComplexPoint τ hτ (projection (P τ) w) := pair_snd τ hτ _ _
  have hax : p≫(action τ hτ a (firstPoint τ hτ)).val=
      candidateComplexPoint τ hτ (projection (P τ) (linear a z)) := by
    change p≫((firstPoint τ hτ).val≫PELOriginalOrderSchemeMorphism318.morphism τ hτ a)=_
    rw [←Category.assoc,hx,PELOriginalOrderSchemeMorphism318.original_point_action]
  have hady : p≫(action τ hτ (adjoint a) (secondPoint τ hτ)).val=
      candidateComplexPoint τ hτ (projection (P τ) (linear (adjoint a) w)) := by
    change p≫((secondPoint τ hτ).val≫PELOriginalOrderSchemeMorphism318.morphism τ hτ (adjoint a))=_
    rw [←Category.assoc,hy,PELOriginalOrderSchemeMorphism318.original_point_action]
  have hadd (f g : Points τ hτ (Product τ hτ) (baseMap τ hτ)) (u v : ComplexVectors)
      (hu : p≫f.val=candidateComplexPoint τ hτ (projection (P τ) u))
      (hv : p≫g.val=candidateComplexPoint τ hτ (projection (P τ) v)) :
      p≫(f+g).val=candidateComplexPoint τ hτ (projection (P τ) (u+v)) := by
    simpa only [PELOriginalAdditionSchemeMorphism318.projection_add] using
      combine_action τ hτ f.val g.val _ p _ _ hu hv
  fin_cases t
  · exact hx
  · exact hy
  · exact hax
  · exact hady
  · exact hadd _ _ _ _ hax hy
  · exact hadd _ _ _ _ hx hady
  · have hn : p≫(-secondPoint τ hτ).val=candidateComplexPoint τ hτ (projection (P τ) (-w)) := by
      change p≫((secondPoint τ hτ).val≫inverse τ hτ)=_
      rw [←Category.assoc,hy,inverse_action,PELOriginalPolarizationSymmetricSquare318.projection_neg]
    simpa only [sub_eq_add_neg] using hadd _ _ _ _ hax hn
  · change p≫((firstPoint τ hτ).val≫PELOriginalOrderSchemeMorphism318.morphism τ hτ (complement a))=_
    rw [←Category.assoc,hx,PELOriginalOrderSchemeMorphism318.original_point_action]
  · change p≫((secondPoint τ hτ).val≫PELOriginalOrderSchemeMorphism318.morphism τ hτ (complement (adjoint a)))=_
    rw [←Category.assoc,hy,PELOriginalOrderSchemeMorphism318.original_point_action]
@[expose] def positions (side : Bool) : Fin 9 → Fin 9 :=
  if side then ![4,0,3,6,7,7,8,3,8] else ![5,2,1,6,7,7,8,3,8]
lemma argument_positions (side : Bool) (z w : ComplexVectors) (i : Fin 9) :
    PELOriginalRosatiPositiveForms318.argument a side z w i=argument a z w (positions side i) := by
  cases side <;> fin_cases i <;>
    simp [PELOriginalRosatiPositiveForms318.argument,PELOriginalRosatiPositiveForms318.first,
      PELOriginalRosatiPositiveForms318.second,argument,positions,linear_zero,linear_one,linear_neg_one,sub_eq_add_neg]
end PELOriginalRosatiProductMaps318
