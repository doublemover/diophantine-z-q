module

public import SelectedSameAAffineChartGauge318
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# The overlap differential in the literal Kähler fibre

The restricted derivation is obtained by quotienting the actual Kähler module by the image of
multiplication by the dual-number generator. Its annihilation property is proved, not a premise.
-/

public section

namespace SelectedSameAAffineFibreDifferential318

open SelectedSameADualNumberFlatCoefficient318 SelectedSameAAffineChartGauge318

variable (k C : Type*) [CommRing k] [CommRing C] [Algebra k C]
  [Algebra (TrivSqZeroExt k k) C]

/-- The actual submodule εΩ of the marked thickened affine. -/
noncomputable def nilpotentDifferentials : Submodule C Ω[C⁄k] :=
  LinearMap.range (LinearMap.lsmul C Ω[C⁄k] (epsilonIn k C))

/-- Restriction of the Kähler module of the thickened affine to its principal fibre. -/
abbrev FibreDifferentials := Ω[C⁄k] ⧸ nilpotentDifferentials k C

theorem epsilon_smul_eq_zero (m : FibreDifferentials k C) :
    epsilonIn k C • m = 0 := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (nilpotentDifferentials k C) m
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change epsilonIn k C • ω ∈
    LinearMap.range (LinearMap.lsmul C Ω[C⁄k] (epsilonIn k C))
  exact ⟨ω, rfl⟩

/-- Universal differential of the same ring, followed by restriction to the actual fibre. -/
noncomputable def reducedD : Derivation k C (FibreDifferentials k C) :=
  (Submodule.mkQ (nilpotentDifferentials k C)).compDer (KaehlerDifferential.D k C)

theorem reducedD_apply (c : C) :
    reducedD k C c = (Submodule.mkQ (nilpotentDifferentials k C)) (KaehlerDifferential.D k C c) := by
  unfold reducedD
  rfl

variable (B : Type*) [CommRing B] [Algebra k B]

/-- The coefficient action on the fibre factors through the same reduction map. -/
theorem smul_eq_of_eq_reduction (ρ : C →ₐ[k] B)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C))
    {x y : C} (h : ρ x = ρ y) (m : FibreDifferentials k C) :
    x • m = y • m := by
  have hxy : x - y ∈ RingHom.ker ρ.toRingHom := RingHom.mem_ker.mpr (by
    change ρ (x - y) = 0
    rw [map_sub, h, sub_self])
  rw [hker] at hxy
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hxy
  apply sub_eq_zero.mp
  rw [← sub_smul, hz, mul_smul, epsilon_smul_eq_zero]

/-- Read the actual differential mismatch on the same quotient, without assuming
an annihilating module, a split frame, or a Kodaira--Spencer matrix. -/
theorem actual_fibre_difference [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →ₐ[k] B) (s₁ s₂ : B →ₐ[k] C)
    (h₁ : ∀ a, ρ (s₁ a) = a) (h₂ : ∀ a, ρ (s₂ a) = a)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C)) (a : B) :
    reducedD k C (s₂ a) - reducedD k C (s₁ a) =
      s₁ (differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker a) •
        reducedD k C (epsilonIn k C) :=
  difference_on_derivatives k C B ρ s₁ s₂ h₁ h₂ hker (reducedD k C) (epsilon_smul_eq_zero k C) a

end SelectedSameAAffineFibreDifferential318
