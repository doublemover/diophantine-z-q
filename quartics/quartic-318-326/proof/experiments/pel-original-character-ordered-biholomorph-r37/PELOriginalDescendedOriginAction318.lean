module
public import PELOriginalWholeInfinityPointImages318
public section
noncomputable section
namespace PELOriginalDescendedOriginAction318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalMaximalQuotient318 PELOriginalKernelStableOpens318
open PELOriginalDescendedLabelMaps318 PELOriginalDescendedLabelAction318
open PELOriginalDescendedCharacterKernel318 PELOriginalWholeInfinityPointImages318

/-- Every original label descends to an automorphism fixing the actual
elliptic origin, as equality of Spec-C-valued scheme morphisms. -/
theorem descended_fixes_origin (i:Fin 4) (a:Labels):
    origin i≫descended i a=origin i:=by
  calc
    origin i≫descended i a=(infinityPoint unitInfinity≫morphism i)≫descended i a :=
      congrArg (fun p=>p≫descended i a) (infinity_image i unitInfinity unitInfinity_zero).symm
    _=infinityPoint (unitInfinity.comp
        (FourRootCoordinateRingSigns318.infinityEnd
          PELOriginalCommonContactBase318.branches (OriginalContactInertiaBasis318.basis a)))≫
        morphism i := by
      rw [Category.assoc,descended_square,←Category.assoc,infinity_point_action]
    _=origin i := infinity_image i _ (signed_infinity_zero unitInfinity a unitInfinity_zero)

/-- Equivariance on all test-scheme morphisms, not merely geometric or
closed points. This is not a claim of universal base-change quotient descent. -/
theorem test_scheme_equivariance {T:Scheme} (i:Fin 4) (a:Labels) (p:T⟶Model):
    (p≫morphism i)≫descended i a=(p≫schemeDeck a)≫morphism i:=by
  rw [Category.assoc,descended_square,←Category.assoc]

/-- The residual involution is a produced nontrivial origin-preserving
scheme automorphism of the SAME ordered Legendre curve. Its identification
with native elliptic negation and the four published quartics is separate. -/
theorem actual_residual_involution (i:Fin 4):
    (residual i).hom≫(residual i).hom=𝟙 (Curve i) ∧
    (residual i).hom≠𝟙 (Curve i) ∧ origin i≫(residual i).hom=origin i:=
  ⟨residual_square i,residual_nontrivial i,
    descended_fixes_origin i (PELOriginalCharacterQuotient318.toggle i)⟩
end PELOriginalDescendedOriginAction318
