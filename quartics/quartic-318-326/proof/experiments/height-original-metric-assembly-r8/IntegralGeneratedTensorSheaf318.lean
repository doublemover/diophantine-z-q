module
public import IntegralOriginalPairGenerators318
public section
noncomputable section
namespace IntegralGeneratedTensorSheaf318
open AlgebraicGeometry CategoryTheory Opposite
open IntegralGluedModel318 IntegralGluedDifferentialFrames318 IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
variable (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))

@[expose] def chosenSection : Option (Fin 4) → Fin 2
  | none => 1
  | some _ => 0

/-- These are the genuine structure-sheaf morphisms represented by the two
original global sections, not new independently chosen local frames. -/
@[expose] def sectionMap (n : Fin 2) :
    SheafOfModules.unit (scheme R c).ringCatSheaf ⟶ tensor R c :=
  ModuleGlobalSections318.ofTop (tensor R c) (q R c hN n)

theorem chosen_generator (i : Option (Fin 4)) (V : (scheme R c).Opens)
    (hV : V≤opens R c i) :
    Function.Bijective (fun a : Γ(scheme R c,V) => a •
      (tensor R c).presheaf.map (homOfLE (show V≤⊤ from le_top)).op
        (q R c hN (chosenSection i))) := by
  cases i with
  | none => exact IntegralOriginalPairGenerators318.global_infinity_generator R c hN V hV
  | some i => exact IntegralOriginalPairGenerators318.global_branch_generator R c hN i V hV

/-- On each actual chart, one of the actual section morphisms is an
isomorphism of O-module SHEAVES. All subopens are checked, not only the
module of global sections on the chart. -/
theorem chart_section_isIso (i : Option (Fin 4)) :
    IsIso ((Scheme.Modules.restrictFunctor (embedding R c i)).map
      (sectionMap R c hN (chosenSection i))) :=
  SectionGeneratorIsomorphism318.restrict_isIso (embedding R c i) (tensor R c)
    (q R c hN (chosenSection i)) (chosen_generator R c hN i)

/-- The original J² pair generates on a whole neighborhood of every actual
scheme point, including finite branch points and the infinity locus. -/
theorem generate_on_neighborhood (x : scheme R c) :
    ∃ (i : Option (Fin 4)), x∈opens R c i ∧
      ∀ (V : (scheme R c).Opens), V≤opens R c i →
        Function.Bijective (fun a : Γ(scheme R c,V) => a •
          (tensor R c).presheaf.map (homOfLE (show V≤⊤ from le_top)).op
            (q R c hN (chosenSection i))) := by
  rcases frames_cover R c hN x with ⟨i,z,hz⟩|⟨z,hz⟩
  · exact ⟨some i,⟨z,trivial,hz⟩,chosen_generator R c hN (some i)⟩
  · exact ⟨none,⟨z,trivial,hz⟩,chosen_generator R c hN none⟩

/-- Every tensor section on a subopen of an original chart is an actual
linear combination of the restrictions of the original two global sections. -/
theorem pair_spans (i : Option (Fin 4)) (V : (scheme R c).Opens)
    (hV : V≤opens R c i) (s : Γ(tensor R c,V)) :
    ∃ a b : Γ(scheme R c,V),
      a • (tensor R c).presheaf.map (homOfLE (show V≤⊤ from le_top)).op (q R c hN 0) +
      b • (tensor R c).presheaf.map (homOfLE (show V≤⊤ from le_top)).op (q R c hN 1)=s := by
  obtain ⟨a,ha⟩ := (chosen_generator R c hN i V hV).2 s
  cases i with
  | none => exact ⟨0,a,by simpa only [zero_smul,zero_add,chosenSection] using ha⟩
  | some i => exact ⟨a,0,by simpa only [zero_smul,add_zero,chosenSection] using ha⟩
end IntegralGeneratedTensorSheaf318
