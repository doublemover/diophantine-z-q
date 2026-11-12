module
public import PELOriginalProjectiveNegation318
public import PELOriginalProperComplexCandidate318
public section
noncomputable section
namespace PELOriginalNegationComplexBase318
open AlgebraicGeometry CategoryTheory HomogeneousLocalization Graded
open PELOriginalCubicRelationIdeal318 PELOriginalNegationRelations318
open PELOriginalProjectiveNegation318 PELOriginalReducedProjectiveCandidate318
open PELOriginalLevelTheta318
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal complex constants in every original homogeneous chart
are fixed by the same graded negation map. -/
lemma away_constant_square {d : ℕ} (s : Equations) (hs : s ∈ degrees d) :
    (Away.map gradedNegation s).comp
      ((fromZeroRingHom degrees (Submonoid.powers s)).comp
        (ComplexProjectiveBase318.constants (ι:=Label 3)).toRingHom) =
      (fromZeroRingHom degrees (Submonoid.powers (gradedNegation s))).comp
        (ComplexProjectiveBase318.constants (ι:=Label 3)).toRingHom := by
  apply RingHom.ext
  intro c
  change Away.map gradedNegation s (Away.mk degrees hs 0 (MvPolynomial.C c) _) =
    Away.mk degrees (gradedNegation.map_mem hs) 0 (MvPolynomial.C c) _
  rw [Away.map_mk]
  have hc : gradedNegation (MvPolynomial.C c) = MvPolynomial.C c :=
    polynomialNegation.commutes c
  rw [hc]

/-- The ambient automorphism preserves the actual degree-zero complex
structure, proved on the true homogeneous affine cover. -/
@[reassoc] theorem ambient_over_complex :
    ambientNegation ≫ ComplexProjectiveBase318.structureMap (ι:=Label 3) =
      ComplexProjectiveBase318.structureMap (ι:=Label 3) := by
  apply (Proj.mapAffineOpenCover gradedNegation irrelevant_le).openCover.hom_ext
  intro s
  simp only [Scheme.AffineOpenCover.openCover_f,Proj.mapAffineOpenCover_f,
    ←Category.assoc,ambientNegation,
    Proj.awayι_comp_map gradedNegation irrelevant_le s.1.2 _ s.2.2]
  simp only [ComplexProjectiveBase318.structureMap,Category.assoc,
    Proj.awayι_toSpecZero_assoc]
  change Spec.map (CommRingCat.ofHom (Away.map gradedNegation s.2.val)) ≫
      (Spec.map (CommRingCat.ofHom (fromZeroRingHom degrees (Submonoid.powers s.2.val))) ≫
        Spec.map (CommRingCat.ofHom (ComplexProjectiveBase318.constants (ι:=Label 3)).toRingHom)) =
    Spec.map (CommRingCat.ofHom
      (fromZeroRingHom degrees (Submonoid.powers (gradedNegation s.2.val)))) ≫
        Spec.map (CommRingCat.ofHom (ComplexProjectiveBase318.constants (ι:=Label 3)).toRingHom)
  simp only [←Spec.map_comp,←CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (away_constant_square s.2.val s.2.property)

variable (τ : ℂ) (hτ : 0 < τ.im)
/-- Genuine automorphism OVER the original complex structure map, not
merely an unbased scheme automorphism or an abstract field automorphism. -/
@[reassoc] theorem candidate_over_complex :
    candidateNegation τ hτ ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ =
      PELOriginalProperComplexCandidate318.structureMap τ hτ := by
  rw [PELOriginalProperComplexCandidate318.structureMap,←Category.assoc,
    candidateNegation_inclusion,Category.assoc,ambient_over_complex]
end PELOriginalNegationComplexBase318
