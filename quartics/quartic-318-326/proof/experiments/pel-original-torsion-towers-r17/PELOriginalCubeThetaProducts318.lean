module
public import PELOriginalFourShiftedSections318
public import PELOriginalLevelThetaNegation318
public import FiniteSeparateTripleExpansion318
public section
noncomputable section
namespace PELOriginalCubeThetaProducts318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalFourShiftedSections318 PELOriginalWholeSectionSpanning318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (4*N)]
abbrev Labels := Fin 7 → Label N
@[expose] def positive (i : Labels N) (x y z : ComplexVectors) : ℂ :=
  value τ hτ N (i 0) (x+y+z)*value τ hτ N (i 1) x*value τ hτ N (i 2) y*
    value τ hτ N (i 3) z*value τ hτ N (i 4) (x-y)*value τ hτ N (i 5) (x-z)*
    value τ hτ N (i 6) (y-z)
@[expose] def negative (i : Labels N) (x y z : ComplexVectors) : ℂ :=
  value τ hτ N (i 0) (x+y)*value τ hτ N (i 1) (x+z)*value τ hτ N (i 2) (y+z)*
    value τ hτ N (i 3) 0*value τ hτ N (i 4) (x-y)*value τ hτ N (i 5) (x-z)*
    value τ hτ N (i 6) (y-z)

lemma positive_x (i : Labels N) (x y z : ComplexVectors) :
    positive τ hτ N i x y z=
      (value τ hτ N (i 2) y*value τ hτ N (i 3) z*value τ hτ N (i 6) (y-z))*
      four τ hτ N ![i 0,i 1,i 4,i 5] ![y+z,0,-y,-z] x := by
  simp only [positive,four,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,←sub_eq_add_neg]
  rw [←add_assoc x y z]
  ring
lemma positive_y (i : Labels N) (x y z : ComplexVectors) :
    positive τ hτ N i x y z=
      (value τ hτ N (i 1) x*value τ hτ N (i 3) z*value τ hτ N (i 5) (x-z))*
      four τ hτ N ![i 0,i 2,-i 4,i 6] ![x+z,0,-x,-z] y := by
  have hsum : y+(x+z)=x+y+z := by abel
  have hneg : x-y= -(y-x) := by abel
  simp only [positive,four,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,←sub_eq_add_neg,
    hsum,hneg,PELOriginalLevelThetaNegation318.value_neg]
  ring
lemma positive_z (i : Labels N) (x y z : ComplexVectors) :
    positive τ hτ N i x y z=
      (value τ hτ N (i 1) x*value τ hτ N (i 2) y*value τ hτ N (i 4) (x-y))*
      four τ hτ N ![i 0,i 3,-i 5,-i 6] ![x+y,0,-x,-y] z := by
  have hsum : z+(x+y)=x+y+z := by abel
  have hx : x-z= -(z-x) := by abel
  have hy : y-z= -(z-y) := by abel
  simp only [positive,four,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,←sub_eq_add_neg,
    hsum,hx,hy,PELOriginalLevelThetaNegation318.value_neg]
  ring
lemma negative_x (i : Labels N) (x y z : ComplexVectors) :
    negative τ hτ N i x y z=
      (value τ hτ N (i 2) (y+z)*value τ hτ N (i 3) 0*value τ hτ N (i 6) (y-z))*
      four τ hτ N ![i 0,i 1,i 4,i 5] ![y,z,-y,-z] x := by
  simp only [negative,four,Matrix.cons_val_zero,Matrix.cons_val_succ,←sub_eq_add_neg]
  ring
lemma negative_y (i : Labels N) (x y z : ComplexVectors) :
    negative τ hτ N i x y z=
      (value τ hτ N (i 1) (x+z)*value τ hτ N (i 3) 0*value τ hτ N (i 5) (x-z))*
      four τ hτ N ![i 0,i 2,-i 4,i 6] ![x,z,-x,-z] y := by
  have hx : x-y= -(y-x) := by abel
  simp only [negative,four,Matrix.cons_val_zero,Matrix.cons_val_succ,←sub_eq_add_neg,
    hx,PELOriginalLevelThetaNegation318.value_neg]
  rw [add_comm y x]
  ring
lemma negative_z (i : Labels N) (x y z : ComplexVectors) :
    negative τ hτ N i x y z=
      (value τ hτ N (i 0) (x+y)*value τ hτ N (i 3) 0*value τ hτ N (i 4) (x-y))*
      four τ hτ N ![i 1,i 2,-i 5,-i 6] ![x,y,-x,-y] z := by
  have hx : x-z= -(z-x) := by abel
  have hy : y-z= -(z-y) := by abel
  simp only [negative,four,Matrix.cons_val_zero,Matrix.cons_val_succ,←sub_eq_add_neg,
    hx,hy,PELOriginalLevelThetaNegation318.value_neg]
  rw [add_comm z x,add_comm z y]
  ring

/-- Six separate spanning proofs use the actual four shifted factors,
including all negative-characteristic changes. No Gram-matrix-only
shortcut discards the original semicharacter. -/
lemma positive_spans (i : Labels N) :
    (∀ y z,∃ c : Label (4*N) → ℂ,∀ x,positive τ hτ N i x y z=∑ k,c k*value τ hτ (4*N) k x) ∧
    (∀ x z,∃ c : Label (4*N) → ℂ,∀ y,positive τ hτ N i x y z=∑ k,c k*value τ hτ (4*N) k y) ∧
    (∀ x y,∃ c : Label (4*N) → ℂ,∀ z,positive τ hτ N i x y z=∑ k,c k*value τ hτ (4*N) k z) := by
  refine ⟨?_,?_,?_⟩
  · intro y z
    obtain ⟨c,hc⟩ := span τ hτ N ![i 0,i 1,i 4,i 5] ![y+z,0,-y,-z] (by change (y+z)+0+ -y+ -z=0; abel)
      (value τ hτ N (i 2) y*value τ hτ N (i 3) z*value τ hτ N (i 6) (y-z))
    exact ⟨c,fun x => (positive_x τ hτ N i x y z).trans (hc x)⟩
  · intro x z
    obtain ⟨c,hc⟩ := span τ hτ N ![i 0,i 2,-i 4,i 6] ![x+z,0,-x,-z] (by change (x+z)+0+ -x+ -z=0; abel)
      (value τ hτ N (i 1) x*value τ hτ N (i 3) z*value τ hτ N (i 5) (x-z))
    exact ⟨c,fun y => (positive_y τ hτ N i x y z).trans (hc y)⟩
  · intro x y
    obtain ⟨c,hc⟩ := span τ hτ N ![i 0,i 3,-i 5,-i 6] ![x+y,0,-x,-y] (by change (x+y)+0+ -x+ -y=0; abel)
      (value τ hτ N (i 1) x*value τ hτ N (i 2) y*value τ hτ N (i 4) (x-y))
    exact ⟨c,fun z => (positive_z τ hτ N i x y z).trans (hc z)⟩
lemma negative_spans (i : Labels N) :
    (∀ y z,∃ c : Label (4*N) → ℂ,∀ x,negative τ hτ N i x y z=∑ k,c k*value τ hτ (4*N) k x) ∧
    (∀ x z,∃ c : Label (4*N) → ℂ,∀ y,negative τ hτ N i x y z=∑ k,c k*value τ hτ (4*N) k y) ∧
    (∀ x y,∃ c : Label (4*N) → ℂ,∀ z,negative τ hτ N i x y z=∑ k,c k*value τ hτ (4*N) k z) := by
  refine ⟨?_,?_,?_⟩
  · intro y z
    obtain ⟨c,hc⟩ := span τ hτ N ![i 0,i 1,i 4,i 5] ![y,z,-y,-z] (by change y+z+ -y+ -z=0; abel)
      (value τ hτ N (i 2) (y+z)*value τ hτ N (i 3) 0*value τ hτ N (i 6) (y-z))
    exact ⟨c,fun x => (negative_x τ hτ N i x y z).trans (hc x)⟩
  · intro x z
    obtain ⟨c,hc⟩ := span τ hτ N ![i 0,i 2,-i 4,i 6] ![x,z,-x,-z] (by change x+z+ -x+ -z=0; abel)
      (value τ hτ N (i 1) (x+z)*value τ hτ N (i 3) 0*value τ hτ N (i 5) (x-z))
    exact ⟨c,fun y => (negative_y τ hτ N i x y z).trans (hc y)⟩
  · intro x y
    obtain ⟨c,hc⟩ := span τ hτ N ![i 1,i 2,-i 5,-i 6] ![x,y,-x,-y] (by change x+y+ -x+ -y=0; abel)
      (value τ hτ N (i 0) (x+y)*value τ hτ N (i 3) 0*value τ hτ N (i 4) (x-y))
    exact ⟨c,fun z => (negative_z τ hτ N i x y z).trans (hc z)⟩

lemma positive_expansion (i : Labels N) :
    ∃ C : Label (4*N) → Label (4*N) → Label (4*N) → ℂ,∀ x y z,
      positive τ hτ N i x y z=∑ a,∑ b,∑ c,C a b c*value τ hτ (4*N) a x*
        value τ hτ (4*N) b y*value τ hτ (4*N) c z := by
  have h := positive_spans τ hτ N i
  exact FiniteSeparateTripleExpansion318.exists_expansion _ _ _
    (original_values_independent τ hτ (4*N)) (original_values_independent τ hτ (4*N))
    _ h.1 h.2.1 h.2.2
lemma negative_expansion (i : Labels N) :
    ∃ C : Label (4*N) → Label (4*N) → Label (4*N) → ℂ,∀ x y z,
      negative τ hτ N i x y z=∑ a,∑ b,∑ c,C a b c*value τ hτ (4*N) a x*
        value τ hτ (4*N) b y*value τ hτ (4*N) c z := by
  have h := negative_spans τ hτ N i
  exact FiniteSeparateTripleExpansion318.exists_expansion _ _ _
    (original_values_independent τ hτ (4*N)) (original_values_independent τ hτ (4*N))
    _ h.1 h.2.1 h.2.2
end PELOriginalCubeThetaProducts318
