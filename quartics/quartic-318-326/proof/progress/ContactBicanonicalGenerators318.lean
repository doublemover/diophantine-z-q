module
public import IntrinsicTensorGenerator318
public import ContactGlobalBicanonical318
public section
noncomputable section
namespace ContactBicanonicalGenerators318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- q0 is a free generator on every subopen of every actual finite chart. -/
theorem branch_generator (i : Fin 4) (V : (ContactGlobalSmooth318.Model c).Opens)
    (hV : V ≤ ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(ContactGlobalSmooth318.Model c,V) => a •
      (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hV).op
        (ContactDirectTensorSections318.branchQ0 c i)) :=
  IntrinsicTensorGenerator318.weighted_generator_bijective
    (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
    (ContactIntrinsicFrames318.branchEmbedding c i) (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (ContactFrameNormalization318.sourceCoordinate c i) (ContactBicanonicalCoefficients318.branchQ0 c i)
    (ContactFrameNormalization318.source_coordinate_normalized c i)
    (ContactBicanonicalCoefficients318.branchQ0_unit c i) V hV

/-- q1 is a free generator on every subopen of the entire infinity chart. -/
theorem infinity_generator (V : (ContactGlobalSmooth318.Model c).Opens)
    (hV : V ≤ InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(ContactGlobalSmooth318.Model c,V) => a •
      (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hV).op
        (ContactDirectTensorSections318.infinityQ1 c)) :=
  IntrinsicTensorGenerator318.weighted_generator_bijective
    (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
    (InfinityGlobalScheme318.chartEmbedding c) (ContactIntrinsicDifferentials318.structureMap c)
    (InfinityStructureSmooth318.chartEmbedding_over_Q c) (ContactDifferentialFrames318.infinityFrame c)
    (ContactFrameNormalization318.infinityCoordinate c) (ContactBicanonicalCoefficients318.infinityQ1 c)
    (ContactFrameNormalization318.infinity_coordinate_normalized c)
    (ContactBicanonicalCoefficients318.infinityQ1_unit c) V hV

/-- The finite-chart generator is the restriction of the actual global q0. -/
theorem global_branch_generator (i : Fin 4) (V : (ContactGlobalSmooth318.Model c).Opens)
    (hV : V ≤ ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(ContactGlobalSmooth318.Model c,V) => a •
      (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (ContactGlobalBicanonical318.q0 c)) := by
  have hr : (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (ContactGlobalBicanonical318.q0 c)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hV).op
      (ContactDirectTensorSections318.branchQ0 c i) := by
    have h1 := congrArg (fun f => f (ContactGlobalBicanonical318.q0 c))
      ((ContactDirectTensorSections318.tensor c).presheaf.map_comp
        (homOfLE (show ContactGlobalBicanonical318.opens c (some i) ≤ ⊤ from le_top)).op (homOfLE hV).op)
    exact h1.trans (congrArg ((ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hV).op)
      (ContactGlobalBicanonical318.q0_restrict c (some i)))
  simpa only [hr] using branch_generator c i V hV

/-- The infinity generator is the restriction of the actual global q1. -/
theorem global_infinity_generator (V : (ContactGlobalSmooth318.Model c).Opens)
    (hV : V ≤ InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(ContactGlobalSmooth318.Model c,V) => a •
      (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (ContactGlobalBicanonical318.q1 c)) := by
  have hr : (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (ContactGlobalBicanonical318.q1 c)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hV).op
      (ContactDirectTensorSections318.infinityQ1 c) := by
    have h1 := congrArg (fun f => f (ContactGlobalBicanonical318.q1 c))
      ((ContactDirectTensorSections318.tensor c).presheaf.map_comp
        (homOfLE (show ContactGlobalBicanonical318.opens c none ≤ ⊤ from le_top)).op (homOfLE hV).op)
    exact h1.trans (congrArg ((ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hV).op)
      (ContactGlobalBicanonical318.q1_restrict c none))
  simpa only [hr] using infinity_generator c V hV

/-- At every actual source point, one of the two actual global sections
freely generates the tensor-square sheaf on a whole open neighborhood. -/
theorem generate_at_every_point (x : ContactGlobalSmooth318.Model c) :
    ∃ V : (ContactGlobalSmooth318.Model c).Opens, x∈V ∧
      (Function.Bijective (fun a : Γ(ContactGlobalSmooth318.Model c,V) => a •
        (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
          (ContactGlobalBicanonical318.q0 c)) ∨
       Function.Bijective (fun a : Γ(ContactGlobalSmooth318.Model c,V) => a •
        (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
          (ContactGlobalBicanonical318.q1 c))) := by
  rcases ContactIntrinsicFrames318.frames_cover c x with ⟨i,q,hq⟩|⟨q,hq⟩
  · exact ⟨ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤,⟨q,trivial,hq⟩,Or.inl (global_branch_generator c i _ le_rfl)⟩
  · exact ⟨InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤,⟨q,trivial,hq⟩,Or.inr (global_infinity_generator c _ le_rfl)⟩
/-- The local generation statement holds on every subopen of the chosen
neighborhood. This is genuine local sheaf generation by q0 or q1, not only
surjectivity on the global sections of one neighborhood. -/
theorem generate_on_neighborhood (x : ContactGlobalSmooth318.Model c) :
    ∃ V : (ContactGlobalSmooth318.Model c).Opens, x∈V ∧
      ((∀ (W : (ContactGlobalSmooth318.Model c).Opens), W≤V →
        Function.Bijective (fun a : Γ(ContactGlobalSmooth318.Model c,W) => a •
          (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
            (ContactGlobalBicanonical318.q0 c))) ∨
       (∀ (W : (ContactGlobalSmooth318.Model c).Opens), W≤V →
        Function.Bijective (fun a : Γ(ContactGlobalSmooth318.Model c,W) => a •
          (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
            (ContactGlobalBicanonical318.q1 c)))) := by
  rcases ContactIntrinsicFrames318.frames_cover c x with ⟨i,q,hq⟩|⟨q,hq⟩
  · exact ⟨ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤,⟨q,trivial,hq⟩,
      Or.inl (fun W hW => global_branch_generator c i W hW)⟩
  · exact ⟨InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤,⟨q,trivial,hq⟩,
      Or.inr (fun W hW => global_infinity_generator c W hW)⟩
end ContactBicanonicalGenerators318
