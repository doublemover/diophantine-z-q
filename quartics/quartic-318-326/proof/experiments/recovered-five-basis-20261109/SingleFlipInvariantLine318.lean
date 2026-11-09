module
public import ActualSourceRationalConstants318
public import CharacterGlobalRegularRatio318
public import ActualFiveRationalIndependent318

public section
noncomputable section
namespace SingleFlipInvariantLine318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open BranchGlobalDifferentialRestriction318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

abbrev X := ContactGlobalSmooth318.Model units
abbrev M := ContactIntrinsicDifferentials318.omega units
local instance modelIntegral : IsIntegral X := ContactProjectiveModel318.model_integral units
attribute [local instance] ActualFiveRationalIndependent318.rationalModule

/-- A single omitted-root involution is sufficient for the omitted branch
divisibility argument. No invariance under the entire eight-sign kernel
is assumed. -/
theorem factorization (i : Fin 4) (s : Γ(M, ⊤))
    (h : ContactDifferentialCharacters318.action (SourceCharacterFields318.flip i) s = s) :
    ∃ a : B i, form i s = (ContactFrameNormalization318.sourceCoordinate units i * a) •
      KaehlerDifferential.D ℚ (B i) (ContactFrameNormalization318.sourceCoordinate units i) := by
  apply BranchDifferentialDivisibility318.fixed_factorization
  exact (form_action i s).symm.trans (congrArg (form i) h)

@[expose] def form_multiple (i : Fin 4) (s : Γ(M, ⊤))
    (h : ContactDifferentialCharacters318.action (SourceCharacterFields318.flip i) s = s) :=
  (factorization i s h).elim (fun a ha =>
    RegularUnitMultiple318.of_factorizations
      (ContactFrameNormalization318.sourceCoordinate units i) a
      (CharacterBranchLocalForm318.unitCoefficient i i)
      (form i s) (CharacterBranchLocalForm318.form i i)
      (KaehlerDifferential.D ℚ (B i) (ContactFrameNormalization318.sourceCoordinate units i))
      (CharacterBranchLocalForm318.unitCoefficient_unit i i) ha
      (CharacterBranchVectorFactorization318.factorization i))

@[expose] def section_multiple (i : Fin 4) (s : Γ(M, ⊤))
    (h : ContactDifferentialCharacters318.action (SourceCharacterFields318.flip i) s = s) :=
  IntrinsicChartLocalMultiple318.section_multiple (X := X) (R := ℚ)
    (S := ContactIntrinsicFrames318.BranchRing units i)
    (ContactIntrinsicDifferentials318.structureMap units) (ContactIntrinsicFrames318.branchEmbedding units i)
    (ContactIntrinsicFrames318.branch_structure units i)
    s (ContactCharacterDifferentials318.differential i) (CharacterBranchLocalForm318.form i i)
    (CharacterBranchActualRestriction318.restrict i i).symm
    (KaehlerModuleMultiple318.to_direct (R := ℚ) (S := B i) (form i s)
      (CharacterBranchLocalForm318.form i i) (form_multiple i s h))

theorem global_multiple (i : Fin 4) (s : Γ(M, ⊤))
    (h : ContactDifferentialCharacters318.action (SourceCharacterFields318.flip i) s = s) :
    ∃ r : Γ(X, ⊤), s = r • ContactCharacterDifferentials318.differential i := by
  have local_multiple (k : Option (Fin 4)) :
      ∃ a : Γ(X, ContactGlobalBicanonical318.opens units k),
        M.presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens units k ≤ ⊤ from le_top)).op s =
        a • M.presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens units k ≤ ⊤ from le_top)).op
          (ContactCharacterDifferentials318.differential i) := by
    cases k with
    | none => exact CharacterUnitChartGeneration318.infinity_multiple i s
    | some j =>
        by_cases hij : i = j
        · subst j; exact section_multiple i s h
        · exact CharacterUnitChartGeneration318.branch_multiple i j hij s
  choose a ha using local_multiple
  exact GlobalScalarMultipleGluing318.exists_global M
    (ContactGlobalBicanonical318.opens units) (ContactGlobalBicanonical318.cover units)
    (ContactGlobalSectionDetection318.common units) (ContactGlobalSectionDetection318.common_le units)
    s (ContactCharacterDifferentials318.differential i) (CharacterCommonScalarInjection318.injective i) a ha

/-- The fixed space of each single original root flip is the line of the
actual complementary elliptic pullback, with original rational scalars. -/
theorem exists_rational_multiple (i : Fin 4) (s : Γ(M, ⊤))
    (h : ContactDifferentialCharacters318.action (SourceCharacterFields318.flip i) s = s) :
    ∃ a : ℚ, s = a • ContactCharacterDifferentials318.differential i := by
  obtain ⟨r, hr⟩ := global_multiple i s h
  obtain ⟨a, ha⟩ := ActualSourceRationalConstants318.constant_bijective.surjective r
  refine ⟨a, ?_⟩
  rw [← ha] at hr
  exact hr

end SingleFlipInvariantLine318
