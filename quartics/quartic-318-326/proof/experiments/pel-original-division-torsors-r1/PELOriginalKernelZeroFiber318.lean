module
public import PELOriginalMultiplicationLocalDivision318
public section
noncomputable section
namespace PELOriginalKernelZeroFiber318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalIntegerMultiplication318
open PELOriginalTorsionKernelScheme318 PELOriginalSchemeAdditionOperations318
open PELOriginalSchemeGroupUnitInverse318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)
abbrev Fiber := pullback (multiplication τ hτ n) (zeroPoint τ hτ)

lemma fiber_base : pullback.fst (multiplication τ hτ n) (zeroPoint τ hτ)≫π τ hτ=
    pullback.snd (multiplication τ hτ n) (zeroPoint τ hτ) := by
  have h := congrArg (fun f => f≫π τ hτ)
    (pullback.condition (f := multiplication τ hτ n) (g := zeroPoint τ hτ))
  simpa only [Category.assoc,over_complex,zero_over,Category.comp_id] using h
@[expose] def toFiber : kernel τ hτ n ⟶ Fiber τ hτ n :=
  pullback.lift (inclusion τ hτ n) (structureMap τ hτ n) (by
    change inclusion τ hτ n≫multiplication τ hτ n=(inclusion τ hτ n≫π τ hτ)≫zeroPoint τ hτ
    rw [Category.assoc]
    exact equalizer.condition _ _)
@[expose] def fromFiber : Fiber τ hτ n ⟶ kernel τ hτ n :=
  equalizer.lift (pullback.fst _ _) (by
    rw [constantZero,←Category.assoc,fiber_base]
    exact pullback.condition)

/-- The original equalizer kernel is the FULL base change over the
actual zero section. Both inverse equations retain all scheme structure. -/
@[expose] def iso : kernel τ hτ n ≅ Fiber τ hτ n where
  hom := toFiber τ hτ n
  inv := fromFiber τ hτ n
  hom_inv_id := by
    apply equalizer.hom_ext
    simp only [toFiber,fromFiber,Category.assoc,equalizer.lift_ι,pullback.lift_fst,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [toFiber,fromFiber,Category.assoc,pullback.lift_fst,equalizer.lift_ι,Category.id_comp]
    · simp only [toFiber,fromFiber,Category.assoc,pullback.lift_snd,structureMap,
        equalizer.lift_ι_assoc,Category.id_comp]
      exact fiber_base τ hτ n
@[reassoc] lemma iso_second : (iso τ hτ n).hom≫pullback.snd _ _=structureMap τ hτ n :=
  pullback.lift_snd _ _ _

/-- Every nonzero integer kernel is finite and smooth over the actual
complex base through the genuine zero-fiber identification. This does
not replace the original equalizer by a reduced zero locus. -/
lemma finite_smooth (hn : n≠0) :
    IsFinite (structureMap τ hτ n) ∧ Smooth (structureMap τ hτ n) := by
  letI := PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn
  letI := PELOriginalMultiplicationSmooth318.smooth τ hτ n hn
  rw [←iso_second]
  exact ⟨inferInstance,inferInstance⟩
lemma flat (hn : n≠0) : Flat (structureMap τ hτ n) := by
  letI := (finite_smooth τ hτ n hn).2
  infer_instance
end PELOriginalKernelZeroFiber318
