module
public import PELOriginalElementaryAction318
public section
noncomputable section
namespace PELOriginalLabeledFixedOrbits318
open QuaternionicJointPeriodTopology318 PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELUnlevelledNormalizerAction318 PELUnlevelledComplexBase318
open PELOriginalPrimeBaseInvolutions318 PELNormOneBaseAction318 PELJointNormOneAction318
open PELOriginalElementaryAction318 PELInertiaArithmeticFixedPoints318
set_option maxHeartbeats 1500000

/-- The actual trace-zero normalizer gives EXACTLY the original labeled
word action, using its explicitly constructed original integral connecting unit. -/
theorem original_label_action (i : Fin 5) (x : UnlevelledBase) :
    coarseAction (inertiaElement i) x=Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • x := by
  let u : normOneUnits := ⟨PELInertiaPrimeWord318.connectingUnit i,
    (mem_normOneUnits _).mpr (PELInertiaPrimeWord318.connectingUnit_norm i)⟩
  have he : inertiaElement i=originalNormalizer u*word (InertiaLabels318.fiveLabels i) := by
    apply Subtype.ext
    apply Units.ext
    exact PELInertiaPrimeWord318.original_label_word i
  rw [he,coarseAction_mul,norm_one_trivial] <;> rfl

@[expose] def originalPoint (i : Fin 5) : UnlevelledBase := projection (originalFixedPoint i)

/-- Each original nonzero inertia label really fixes its ORIGINAL point
under the faithful elementary2 action, not an independently selected involution. -/
theorem original_label_fixes (i : Fin 5) :
    Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • originalPoint i=originalPoint i := by
  rw [←original_label_action]
  change coarseAction (inertiaElement i) (projection (originalFixedPoint i))= _
  rw [coarseAction_square,original_fixed]

theorem original_label_nontrivial (i : Fin 5) :
    actionHom (Multiplicative.ofAdd (InertiaLabels318.fiveLabels i))≠1 := by
  intro h
  have he := actionHom_injective (h.trans actionHom.map_one.symm)
  exact InertiaLabels318.five_labels_nonzero i (congrArg Multiplicative.toAdd he)

/-- The five displayed fixed points lie in distinct orbits of the ACTUAL
faithful16-group. No assertion that these exhaust all branch orbits is made. -/
theorem distinct_labeled_orbits (v : Multiplicative InertiaLabels318.V) (i j : Fin 5)
    (h : v • originalPoint i=originalPoint j) : i=j := by
  apply PELUnlevelledInertiaOrbits318.index_of_unlevelled_normalizer_orbit
    (word (Multiplicative.toAdd v)) i j
  change coarseAction (word (Multiplicative.toAdd v)) (projection (originalFixedPoint i))=
    projection (originalFixedPoint j) at h
  rwa [coarseAction_square] at h
end PELOriginalLabeledFixedOrbits318
