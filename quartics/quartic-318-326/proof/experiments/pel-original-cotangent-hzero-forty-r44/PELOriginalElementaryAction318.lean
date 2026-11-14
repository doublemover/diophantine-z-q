module
public import PELOriginalWordNormCocycle318
public section
noncomputable section
namespace PELOriginalElementaryAction318
open PELPositiveOrderNormalizer318 PELUnlevelledNormalizerAction318 PELUnlevelledComplexBase318
open PELActualSquareNormActionKernel318 PELOriginalWordActionFaithful318 PELOriginalWordNormCocycle318
set_option maxHeartbeats 1700000

theorem word_action_add (v w : InertiaLabels318.V) (x : UnlevelledBase) :
    coarseAction (word (v+w)) x=coarseAction (word v) (coarseAction (word w) x) := by
  have hk := square_norm_identity ((word (v+w))⁻¹*word v*word w)
    (Units.mk0 (squareFactor v w) (squareFactor_nonzero v w)) (discrepancy_square v w) x
  have he := congrArg (coarseAction (word (v+w))) hk
  rw [←coarseAction_mul] at he
  have hg : word (v+w)*((word (v+w))⁻¹*word v*word w)=word v*word w := by group
  rw [hg,coarseAction_mul] at he
  exact he.symm

theorem word_zero : word (0:InertiaLabels318.V)=1 := by
  apply Subtype.ext
  simp [PELPositiveOrderNormalizer318.word,PELInertiaPrimeWord318.word]

theorem word_action_zero (x : UnlevelledBase) : coarseAction (word 0) x=x := by
  rw [word_zero,coarseAction_one]

/-- A genuine faithful action of the ORIGINAL elementary2 label group on
the actual unlevelled complex curve. Every group law is supplied by the
full original word norm cocycle and actual action-kernel theorem. -/
@[expose] def actionHom : Multiplicative InertiaLabels318.V →* Equiv.Perm UnlevelledBase where
  toFun v := coarseEquiv (word (Multiplicative.toAdd v))
  map_one' := by ext x; exact word_action_zero x
  map_mul' v w := by ext x; exact word_action_add _ _ x

theorem actionHom_injective : Function.Injective actionHom := by
  intro v w h
  have he : coarseAction (word (Multiplicative.toAdd v))=
      coarseAction (word (Multiplicative.toAdd w)) := congrArg (fun e : Equiv.Perm UnlevelledBase => (e:UnlevelledBase→UnlevelledBase)) h
  have hvw := original_word_action_injective he
  exact congrArg Multiplicative.ofAdd hvw

instance originalAction : MulAction (Multiplicative InertiaLabels318.V) UnlevelledBase where
  smul v x := actionHom v x
  one_smul x := word_action_zero x
  mul_smul v w x := word_action_add _ _ x

theorem actual_word_action (v : InertiaLabels318.V) (x : UnlevelledBase) :
    Multiplicative.ofAdd v • x=coarseAction (word v) x := rfl

theorem action_faithful (v w : Multiplicative InertiaLabels318.V)
    (h : ∀ x : UnlevelledBase,v • x=w • x) : v=w :=
  actionHom_injective (Equiv.ext h)

open scoped Manifold ContDiff
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

theorem original_action_holomorphic (v : Multiplicative InertiaLabels318.V) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x : UnlevelledBase => v • x) :=
  coarseAction_holomorphic (word (Multiplicative.toAdd v))
end PELOriginalElementaryAction318
