module
public import ThreeTorsionSplitEval318
public import ThreeTorsionLabels318
public section
noncomputable section
namespace ThreeTorsionDiamond318
open Polynomial ThreeTorsionAlgebra318 ThreeTorsionSplitData318
open ThreeTorsionSplitEval318 ThreeTorsionInvolution318 ThreeTorsionLabels318
open InvariantBaseChange318 PrimitiveDiamond318
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R] [Nontrivial R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

@[expose] def diamond (g:(ZMod 3)ˣ) : Ring A B hD≃ₐ[R]Ring A B hD :=
  if g=1 then AlgEquiv.refl else negEquiv A B hD
@[simp] theorem diamond_one : diamond A B hD 1=AlgEquiv.refl := by simp [diamond]
@[simp] theorem diamond_neg_one : diamond A B hD (-1)=negEquiv A B hD := by
  simp only [diamond,neg_one_ne_one,if_false]

theorem diamond_mul (g h:(ZMod 3)ˣ) (b:Ring A B hD) :
    diamond A B hD (g*h) b=diamond A B hD g (diamond A B hD h b) := by
  rcases unit_cases g with rfl|rfl <;> rcases unit_cases h with rfl|rfl
  · simp
  · simp
  · simp
  · simpa using (negEquiv_involutive A B hD b).symm

lemma signedY_flip (i:ThreeTorsionLabels318.Index) :
    signedY A B hD (flip i)= -signedY A B hD i := by
  rcases i with ⟨i,b⟩
  cases b <;> simp [signedY,ThreeTorsionLabels318.flip]

lemma evaluate_neg (i:ThreeTorsionLabels318.Index) (b:Ring A B hD) :
    evaluate A B hD i (negEquiv A B hD b)=evaluate A B hD (flip i) b := by
  have hh:(evaluate A B hD i).comp (negEquiv A B hD).toAlgHom=
      evaluate A B hD (flip i):=by
    apply ThreeTorsionFunctor318.hom_ext
    · simp [ThreeTorsionLabels318.flip]
    · simp [signedY_flip]
  exact AlgHom.congr_fun hh b

lemma split_neg (z:T A B hD⊗[R]Ring A B hD) (i:ThreeTorsionLabels318.Index) :
    ThreeTorsionSplitEval318.splitEquiv A B hD
      (baseAction (T A B hD) (fun _:Unit=>negEquiv A B hD) () z) i=
        ThreeTorsionSplitEval318.splitEquiv A B hD z (flip i) := by
  induction z using TensorProduct.inductionOn with
  | tmul s b => rw [baseAction_tmul,splitEquiv_tmul,splitEquiv_tmul,evaluate_neg]
  | add z w hz hw => simp only [map_add,Pi.add_apply,hz,hw]

@[expose] def primitiveSplit :
    T A B hD⊗[R]Ring A B hD≃ₐ[T A B hD](Points 3→T A B hD) :=
  (ThreeTorsionSplitEval318.splitEquiv A B hD).trans
    (AlgEquiv.piCongrLeft' (T A B hD) (fun _=>T A B hD) labels)

lemma primitiveSplit_label (z:T A B hD⊗[R]Ring A B hD) (i:ThreeTorsionLabels318.Index) :
    primitiveSplit A B hD z (label i)=ThreeTorsionSplitEval318.splitEquiv A B hD z i := by
  change ThreeTorsionSplitEval318.splitEquiv A B hD z (labels.symm (labels i))=_
  rw [Equiv.symm_apply_apply]

/-- Full diamond-equivariance for the actual primitive modulo-three pairs.
The nontrivial unit exchanges the two y signs and fixes the four x-roots. -/
theorem equivariant (g:(ZMod 3)ˣ) (z:T A B hD⊗[R]Ring A B hD) (p:Points 3) :
    primitiveSplit A B hD (baseAction (T A B hD) (diamond A B hD) g z) p=
      primitiveSplit A B hD z (g•p) := by
  obtain ⟨i,rfl⟩:=label_bijective.2 p
  rcases unit_cases g with rfl|rfl
  · simp only [one_smul]
    congr 1
    simp [baseAction,diamond]
  · rw [←label_flip,primitiveSplit_label,primitiveSplit_label]
    change ThreeTorsionSplitEval318.splitEquiv A B hD
      (baseAction (T A B hD) (fun _:Unit=>negEquiv A B hD) () z) i=_
    exact split_neg A B hD z i

end ThreeTorsionDiamond318
