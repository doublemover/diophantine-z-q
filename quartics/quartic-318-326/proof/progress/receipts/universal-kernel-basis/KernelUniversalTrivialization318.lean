module
public import KernelUniversalGeometricBasis318
public import LiteralIndependentPairRank318
public section
noncomputable section
namespace KernelUniversalTrivialization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KernelUniversalFrame318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N : ℕ) [NeZero N]
/-- Actual full kernel trivialization over the original rank48 independent-pair cover.
The component labelled c is the genuine c0*P+c1*Q section, not an arbitrary splitting label. -/
@[expose] def iso : (∐ fun _ : Fin 2 → ZMod 3 => Frame N) ≅ family N :=
  EtaleSectionTrivialization318.iso (projection N) (sectionMap N) (section_projection N)
    (KernelUniversalGeometricBasis318.all_geometric N)
@[reassoc] theorem component (c : Fin 2 → ZMod 3) :
    Sigma.ι (fun _ : Fin 2 → ZMod 3 => Frame N) c ≫ (iso N).hom = sectionMap N c :=
  EtaleSectionTrivialization318.component _ _ _ _ c
@[reassoc] theorem component_original (c : Fin 2 → ZMod 3) :
    Sigma.ι (fun _ : Fin 2 → ZMod 3 => Frame N) c ≫ (iso N).hom ≫ original N =
      (combination N c).val := by rw [component_assoc,section_original]
@[reassoc] theorem over_frame : (iso N).hom ≫ projection N =
    Sigma.desc (fun _ : Fin 2 → ZMod 3 => 𝟙 (Frame N)) :=
  EtaleSectionTrivialization318.base _ _ _ _

/-- The two standard coefficient vectors recover the two original universal kernel points. -/
@[simp] theorem first_standard : combination N ![1,0] = first N := by simp [combination]
@[simp] theorem second_standard : combination N ![0,1] = second N := by simp [combination]
@[simp] theorem zero_standard : combination N 0 = 0 := by simp [combination]
/-- The labels are now tied to the genuine represented addition. -/
theorem addition (c d : Fin 2 → ZMod 3) : combination N (c+d) = combination N c + combination N d := by
  simp only [combination,Pi.add_apply,add_smul]
  abel
/-- Actual finite-etale surjective cover on which this explicit trivialization is constructed. -/
theorem cover : IsFinite (frameBase N) ∧ Etale (frameBase N) ∧ Surjective (frameBase N) :=
  LiteralIndependentPairRank318.finite_etale_surjective N
end KernelUniversalTrivialization318
