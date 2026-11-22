module

public import SelectedSameAAffineFibreDifferential318
public import SelectedSameAADualNumberAffineChart318
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Abel
import all SelectedSameAAffineFibreDifferential318

/-!
# The coefficient of the actual nilpotent differential

The coefficient map is derived from the genuine chosen affine section,
its entire dual-number chart, and the universal differential. It is
not a supplied retraction of an unrelated module.
-/

public section

namespace SelectedSameACechEpsilonReadout318

open MulOpposite
open SelectedSameADualNumberFlatCoefficient318
open SelectedSameAADualNumberAffineChart318
open SelectedSameAAffineFibreDifferential318
open SelectedSameAAffineChartGauge318

variable (k C B : Type*) [CommRing k] [CommRing C] [CommRing B]
  [Algebra k C] [Algebra k B] [Algebra (TrivSqZeroExt k k) C]
  [hFlat : Module.Flat (TrivSqZeroExt k k) C]
  [Algebra C B] [IsScalarTower k C B]
variable (ρ : C →ₐ[k] B) (s : B →ₐ[k] C) (hs : ∀ a, ρ (s a) = a)
  (hk : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C))
  (hρ : algebraMap C B = ρ.toRingHom)

include hρ in
private theorem residueSMul (c : C) (b : B) : c • b = ρ c * b := by
  rw [Algebra.smul_def, hρ]
  rfl

include hFlat hs hk

private noncomputable def literalChart : TrivSqZeroExt B B ≃+* C :=
  chartOfSection k C B s.toRingHom ρ.toRingHom hs hk

private theorem literalChart_apply (x : TrivSqZeroExt B B) :
    literalChart k C B ρ s hs hk x = s x.fst + epsilonIn k C * s x.snd :=
  chartOfSection_apply k C B s.toRingHom ρ.toRingHom hs hk x

/-- Read the second coordinate in the whole ring chart of the given section. -/
noncomputable def coefficient (c : C) : B := ((literalChart k C B ρ s hs hk).symm c).snd

private theorem fst_inverse (c : C) : ((literalChart k C B ρ s hs hk).symm c).fst = ρ c := by
  let E := literalChart k C B ρ s hs hk
  let z := E.symm c
  have hε : ρ (epsilonIn k C) = 0 := map_epsilon_eq_zero k C B ρ.toRingHom hk
  have h : ρ (E z) = z.fst := by
    change ρ (literalChart k C B ρ s hs hk z) = z.fst
    rw [literalChart_apply, map_add, map_mul, hε, hs, zero_mul, add_zero]
  exact h.symm.trans (congrArg ρ (E.apply_symm_apply c))

private theorem inverse_on_section (a : B) :
    (literalChart k C B ρ s hs hk).symm (s a) = TrivSqZeroExt.inl a := by
  apply (literalChart k C B ρ s hs hk).injective
  rw [RingEquiv.apply_symm_apply]
  symm
  rw [literalChart_apply]
  simp only [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, map_zero, mul_zero, add_zero]

private theorem inverse_on_epsilon :
    (literalChart k C B ρ s hs hk).symm (epsilonIn k C) = TrivSqZeroExt.inr 1 := by
  apply (literalChart k C B ρ s hs hk).injective
  rw [RingEquiv.apply_symm_apply]
  symm
  rw [literalChart_apply]
  simp only [TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, map_one, mul_one, zero_add]

theorem coefficient_on_section (a : B) : coefficient k C B ρ s hs hk (s a) = 0 := by
  unfold coefficient
  rw [inverse_on_section, TrivSqZeroExt.snd_inl]

theorem coefficient_on_epsilon : coefficient k C B ρ s hs hk (epsilonIn k C) = 1 := by
  unfold coefficient
  rw [inverse_on_epsilon, TrivSqZeroExt.snd_inr]

include hρ in
/-- The actual chart coefficient is a derivation over the actual residue action. -/
noncomputable def coefficientDerivation : Derivation k C B := by
  refine Derivation.mk' ?_ ?_
  · refine { toFun := coefficient k C B ρ s hs hk, map_add' := ?_, map_smul' := ?_ }
    · intro x y
      unfold coefficient
      rw [map_add, TrivSqZeroExt.snd_add]
    · intro a x
      change coefficient k C B ρ s hs hk (a • x) = a • coefficient k C B ρ s hs hk x
      have hw : (literalChart k C B ρ s hs hk).symm (algebraMap k C a) = TrivSqZeroExt.inl (algebraMap k B a) := by
        rw [← s.commutes, inverse_on_section]
      unfold coefficient
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hw, TrivSqZeroExt.snd_mul]
      simp only [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul]
  · intro x y
    change coefficient k C B ρ s hs hk (x * y) =
      x • coefficient k C B ρ s hs hk y + y • coefficient k C B ρ s hs hk x
    have hm (a : C) (b : B) : a • b = ρ a * b := by
      rw [Algebra.smul_def, hρ]
      rfl
    unfold coefficient
    simp only [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, smul_eq_mul, fst_inverse, hm]

include hρ in
/-- Descend the universal coefficient to the actual quotient by epsilon
times the absolute differential module. -/
noncomputable def fibreReadout : FibreDifferentials k C →ₗ[C] B := by
  refine (nilpotentDifferentials k C).liftQ
    (coefficientDerivation k C B ρ s hs hk hρ).liftKaehlerDifferential ?_
  intro ω hω
  unfold nilpotentDifferentials at hω
  obtain ⟨v, hv⟩ := hω
  change epsilonIn k C • v = ω at hv
  rw [← hv, LinearMap.mem_ker, LinearMap.map_smul]
  rw [residueSMul k C B ρ hρ, map_epsilon_eq_zero k C B ρ.toRingHom hk, zero_mul]

/-- Evaluation on a genuine differential is the same actual chart coefficient. -/
theorem fibreReadout_D (c : C) :
    fibreReadout k C B ρ s hs hk hρ (reducedD k C c) = coefficient k C B ρ s hs hk c := by
  unfold fibreReadout
  rw [reducedD_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
    Derivation.liftKaehlerDifferential_comp_D] <;> rfl

/-- The nilpotent differential has coefficient one on the actual fibre.
This is a retraction even though the fibre map need not be flat. -/
theorem fibreReadout_dEpsilon (c : C) :
    fibreReadout k C B ρ s hs hk hρ (c • reducedD k C (epsilonIn k C)) = ρ c := by
  rw [LinearMap.map_smul, fibreReadout_D, coefficient_on_epsilon]
  rw [residueSMul k C B ρ hρ, mul_one]

/-- With any one common reference section of the true differential
module on the overlap, the two scalar corrections have the exact
signed gauge difference. In use m is the restriction of the same
global lift of da from the actual connecting sequence. -/
theorem overlap_readout_after_common
    (s' : B →ₐ[k] C) (hs' : ∀ a, ρ (s' a) = a)
    (a : B) (m : FibreDifferentials k C) :
    fibreReadout k C B ρ s hs hk hρ (reducedD k C (s' a) - m) -
      fibreReadout k C B ρ s hs hk hρ (reducedD k C (s a) - m) =
        differenceDerivation k C B ρ s s' hs hs' hk a := by
  let f := fibreReadout k C B ρ s hs hk hρ
  calc
    _ = f (reducedD k C (s' a) - reducedD k C (s a)) := by
      change f (reducedD k C (s' a) - m) - f (reducedD k C (s a) - m) = _
      simp only [map_sub]
      abel
    _ = _ := by
      change fibreReadout k C B ρ s hs hk hρ
        (reducedD k C (s' a) - reducedD k C (s a)) = _
      rw [actual_fibre_difference k C B ρ s s' hs hs' hk, fibreReadout_dEpsilon, hs]

section ActualCorrection

variable [Module B (FibreDifferentials k C)] [IsScalarTower k B (FibreDifferentials k C)]
variable (hAct : ∀ (b : B) (m : FibreDifferentials k C), b • m = s b • m)

include hρ hAct in
private noncomputable def bReadout : FibreDifferentials k C →ₗ[B] B :=
  { toFun := fibreReadout k C B ρ s hs hk hρ
    map_add' := (fibreReadout k C B ρ s hs hk hρ).map_add
    map_smul' := fun b m => by
      change fibreReadout k C B ρ s hs hk hρ (b • m) =
        b • fibreReadout k C B ρ s hs hk hρ m
      rw [hAct b, LinearMap.map_smul]
      rw [residueSMul k C B ρ hρ, hs] <;> exact (smul_eq_mul b _).symm }

include hAct in
private noncomputable def sectionDerivative : Derivation k B (FibreDifferentials k C) :=
  Derivation.mk' ((reducedD k C).toLinearMap.comp s.toLinearMap) (by
    intro a b
    change reducedD k C (s (a * b)) =
      a • reducedD k C (s b) + b • reducedD k C (s a)
    rw [map_mul s, Derivation.leibniz, hAct a, hAct b])

include hρ hAct in
/-- Once the actual global differential splitting has been restricted
and composed with the universal derivation (g), take its genuine
affine correction. This produces a derivation, rather than presupposing it. -/
noncomputable def correctionDerivation
    (g : Derivation k B (FibreDifferentials k C)) : Derivation k B B :=
  (bReadout k C B ρ s hs hk hρ hAct).compDer (sectionDerivative k C B s hAct - g)

theorem correctionDerivation_apply (g : Derivation k B (FibreDifferentials k C)) (a : B) :
    correctionDerivation k C B ρ s hs hk hρ hAct g a =
      fibreReadout k C B ρ s hs hk hρ (reducedD k C (s a) - g a) := by
  unfold correctionDerivation
  change fibreReadout k C B ρ s hs hk hρ ((sectionDerivative k C B s hAct - g) a) = _
  rw [Derivation.sub_apply] <;> rfl

end ActualCorrection

end SelectedSameACechEpsilonReadout318
