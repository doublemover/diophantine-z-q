module

public import SelectedSameAADualNumberAffineChart318
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.Ring

/-!
# Exact gauge of two genuine affine sections

For two sections of the same principal square-zero reduction, derive the derivation as the
unique coefficient of their actual difference. The chart transition is evaluated on the
whole dual-number ring, not just its reduction. Flatness is over the dual numbers.
-/

public section

namespace SelectedSameAAffineChartGauge318

open SelectedSameADualNumberFlatCoefficient318 SelectedSameAADualNumberAffineChart318

variable (k C B : Type*) [CommRing k] [CommRing C] [CommRing B]
  [Algebra (TrivSqZeroExt k k) C] [Algebra k C] [Algebra k B]

/-- Multiplication by the nilpotent generator reads only the actual reduction of a lift. -/
theorem epsilon_mul_eq_of_eq_reduction (ρ : C →ₐ[k] B)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C))
    {x y : C} (h : ρ x = ρ y) :
    epsilonIn k C * x = epsilonIn k C * y := by
  have hr : x - y ∈ RingHom.ker ρ.toRingHom := RingHom.mem_ker.mpr (by
    change ρ (x - y) = 0
    rw [map_sub, h, sub_self])
  rw [hker] at hr
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hr
  apply sub_eq_zero.mp
  rw [← mul_sub, hv, ← mul_assoc, epsilonIn_square, zero_mul]

private theorem epsilon_lift_injective [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →ₐ[k] B) (s : B →ₐ[k] C) (hs : ∀ a, ρ (s a) = a)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C)) :
    Function.Injective (fun a : B => epsilonIn k C * s a) := by
  intro a b h
  have hz : ρ.toRingHom (epsilonIn k C * s b) = 0 := by
    rw [map_mul, map_epsilon_eq_zero k C B ρ.toRingHom hker, zero_mul]
  obtain ⟨c, _, hu⟩ := existsUnique_coefficient k C ρ.toRingHom s.toRingHom hs hker _ hz
  exact (hu a h).trans (hu b rfl).symm

section Difference

variable [Module.Flat (TrivSqZeroExt k k) C]
variable (ρ : C →ₐ[k] B) (s₁ s₂ : B →ₐ[k] C)
variable (h₁ : ∀ a, ρ (s₁ a) = a) (h₂ : ∀ a, ρ (s₂ a) = a)
variable (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C))

include ρ h₁ h₂ hker

/-- Existence and uniqueness for the actual first-order difference, before assuming Leibniz. -/
theorem existsUnique_differenceCoefficient (a : B) :
    ∃! b : B, epsilonIn k C * s₁ b = s₂ a - s₁ a := by
  have hz : ρ.toRingHom (s₂ a - s₁ a) = 0 := by
    change ρ (s₂ a - s₁ a) = 0
    rw [map_sub, h₂, h₁, sub_self]
  exact existsUnique_coefficient k C ρ.toRingHom s₁.toRingHom h₁ hker _ hz

private noncomputable def differenceCoefficient (a : B) : B :=
  Classical.choose (existsUnique_differenceCoefficient k C B ρ s₁ s₂ h₁ h₂ hker a).exists

private theorem differenceCoefficient_beta (a : B) :
    epsilonIn k C * s₁ (differenceCoefficient k C B ρ s₁ s₂ h₁ h₂ hker a) =
      s₂ a - s₁ a :=
  Classical.choose_spec (existsUnique_differenceCoefficient k C B ρ s₁ s₂ h₁ h₂ hker a).exists

/-- The actual sections induce a genuine derivation over the same residue constants. -/
noncomputable def differenceDerivation : Derivation k B B := by
  let e := epsilonIn k C
  let d := differenceCoefficient k C B ρ s₁ s₂ h₁ h₂ hker
  have H (a : B) : e * s₁ (d a) = s₂ a - s₁ a :=
    differenceCoefficient_beta k C B ρ s₁ s₂ h₁ h₂ hker a
  have hi : Function.Injective (fun a : B => e * s₁ a) :=
    epsilon_lift_injective k C B ρ s₁ h₁ hker
  have hscalar (s : B →ₐ[k] C) (r : k) (a : B) :
      s (r • a) = algebraMap k C r * s a := by
    rw [Algebra.smul_def, map_mul, s.commutes]
  let L : B →ₗ[k] B := {
    toFun := d
    map_add' := fun a b => hi (by
      calc
        e * s₁ (d (a + b)) = s₂ (a + b) - s₁ (a + b) := H _
        _ = (s₂ a - s₁ a) + (s₂ b - s₁ b) := by
          rw [map_add s₂, map_add s₁]
          ring
        _ = e * s₁ (d a + d b) := by
          rw [map_add s₁, mul_add, H a, H b])
    map_smul' := fun r a => hi (by
      change e * s₁ (d (r • a)) = e * s₁ (r • d a)
      calc
        e * s₁ (d (r • a)) = s₂ (r • a) - s₁ (r • a) := H _
        _ = algebraMap k C r * (s₂ a - s₁ a) := by
          rw [hscalar s₂, hscalar s₁, mul_sub]
        _ = e * s₁ (r • d a) := by
          rw [hscalar s₁, ← H a]
          ring) }
  refine Derivation.mk' L (fun a b => ?_)
  change d (a * b) = a * d b + b * d a
  apply hi
  have hnil : (s₂ a - s₁ a) * (s₂ b - s₁ b) = 0 := by
    rw [← H a, ← H b]
    calc
      (e * s₁ (d a)) * (e * s₁ (d b)) =
          (e * e) * (s₁ (d a) * s₁ (d b)) := by ring
      _ = 0 := by
        have he : e * e = 0 := epsilonIn_square k C
        rw [he, zero_mul]
  calc
    e * s₁ (d (a * b)) = s₂ (a * b) - s₁ (a * b) := H _
    _ = (s₁ a * (s₂ b - s₁ b) + s₁ b * (s₂ a - s₁ a)) +
        (s₂ a - s₁ a) * (s₂ b - s₁ b) := by
      rw [map_mul s₂, map_mul s₁]
      ring
    _ = s₁ a * (s₂ b - s₁ b) + s₁ b * (s₂ a - s₁ a) := by rw [hnil, add_zero]
    _ = e * s₁ (a * d b + b * d a) := by
      rw [← H a, ← H b]
      simp only [map_add, map_mul, mul_add]
      ring

theorem differenceDerivation_beta (a : B) :
    epsilonIn k C * s₁ (differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker a) =
      s₂ a - s₁ a := by
  unfold differenceDerivation
  change epsilonIn k C * s₁ (differenceCoefficient k C B ρ s₁ s₂ h₁ h₂ hker a) =
    s₂ a - s₁ a
  exact differenceCoefficient_beta k C B ρ s₁ s₂ h₁ h₂ hker a

theorem differenceDerivation_unique (d : Derivation k B B)
    (hd : ∀ a, epsilonIn k C * s₁ (d a) = s₂ a - s₁ a) :
    d = differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker := by
  apply Derivation.ext
  intro a
  apply epsilon_lift_injective k C B ρ s₁ h₁ hker
  exact (hd a).trans (differenceDerivation_beta k C B ρ s₁ s₂ h₁ h₂ hker a).symm

/-- From coordinates of section two to coordinates of section one, over the same reduction. -/
noncomputable def chartTransition : TrivSqZeroExt B B ≃+* TrivSqZeroExt B B :=
  (chartOfSection k C B s₂.toRingHom ρ.toRingHom h₂ hker).trans
    (chartOfSection k C B s₁.toRingHom ρ.toRingHom h₁ hker).symm

/-- Exact unreduced coordinate chart change. The first coordinate and constants stay fixed. -/
theorem chartTransition_apply (x : TrivSqZeroExt B B) :
    chartTransition k C B ρ s₁ s₂ h₁ h₂ hker x =
      ((x.fst, x.snd + differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker x.fst) :
        TrivSqZeroExt B B) := by
  let F₁ := chartOfSection k C B s₁.toRingHom ρ.toRingHom h₁ hker
  let F₂ := chartOfSection k C B s₂.toRingHom ρ.toRingHom h₂ hker
  unfold chartTransition
  change F₁.symm (F₂ x) =
    ((x.fst, x.snd + differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker x.fst) :
      TrivSqZeroExt B B)
  apply F₁.injective
  rw [RingEquiv.apply_symm_apply]
  change chartOfSection k C B s₂.toRingHom ρ.toRingHom h₂ hker x =
    chartOfSection k C B s₁.toRingHom ρ.toRingHom h₁ hker
      ((x.fst, x.snd + differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker x.fst) :
        TrivSqZeroExt B B)
  rw [chartOfSection_apply k C B s₂.toRingHom, chartOfSection_apply k C B s₁.toRingHom]
  simp only [TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, map_add, mul_add]
  change s₂ x.fst + epsilonIn k C * s₂ x.snd =
    s₁ x.fst + (epsilonIn k C * s₁ x.snd +
      epsilonIn k C * s₁ (differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker x.fst))
  rw [← epsilon_mul_eq_of_eq_reduction k C B ρ hker ((h₁ x.snd).trans (h₂ x.snd).symm),
    differenceDerivation_beta]
  ring

/-- Equality of the two maps into the actual chart ring, before any reduction. -/
theorem second_chart_eq_first_after_gauge (x : TrivSqZeroExt B B) :
    chartOfSection k C B s₂.toRingHom ρ.toRingHom h₂ hker x =
      chartOfSection k C B s₁.toRingHom ρ.toRingHom h₁ hker
        (chartTransition k C B ρ s₁ s₂ h₁ h₂ hker x) := by
  unfold chartTransition
  exact ((chartOfSection k C B s₁.toRingHom ρ.toRingHom h₁ hker).apply_symm_apply _).symm

/-- The signed cocycle law on one common affine with three genuine sections. -/
theorem differenceDerivation_cocycle (s₃ : B →ₐ[k] C)
    (h₃ : ∀ a, ρ (s₃ a) = a) :
    differenceDerivation k C B ρ s₁ s₃ h₁ h₃ hker =
      differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker +
      differenceDerivation k C B ρ s₂ s₃ h₂ h₃ hker := by
  let d := differenceDerivation k C B ρ s₂ s₃ h₂ h₃ hker
  apply Derivation.ext
  intro a
  apply epsilon_lift_injective k C B ρ s₁ h₁ hker
  rw [Derivation.add_apply, map_add, mul_add,
    differenceDerivation_beta k C B ρ s₁ s₃,
    differenceDerivation_beta k C B ρ s₁ s₂]
  change s₃ a - s₁ a = s₂ a - s₁ a + epsilonIn k C * s₁ (d a)
  rw [epsilon_mul_eq_of_eq_reduction k C B ρ hker ((h₁ (d a)).trans (h₂ (d a)).symm)]
  have hd : epsilonIn k C * s₂ (d a) = s₃ a - s₂ a :=
    differenceDerivation_beta k C B ρ s₂ s₃ h₂ h₃ hker a
  rw [hd]
  ring

/-- The actual difference on differential lifts after reduction. In the Kähler module
of the thickened affine restricted to the fibre, the hypothesis holds for the generator. -/
theorem difference_on_derivatives {M : Type*} [AddCommGroup M] [Module C M] [Module k M]
    (D : Derivation k C M) (hε : ∀ m : M, epsilonIn k C • m = 0) (a : B) :
    D (s₂ a) - D (s₁ a) =
      s₁ (differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker a) • D (epsilonIn k C) := by
  rw [← D.map_sub, ← differenceDerivation_beta k C B ρ s₁ s₂ h₁ h₂ hker a,
    D.leibniz, hε, zero_add]

end Difference

section Correction

/-- Translate an actual section by a chosen residue derivation, over the same constants. -/
def adjustSection (s : B →ₐ[k] C) (d : Derivation k B B) : B →ₐ[k] C where
  toFun a := s a + epsilonIn k C * s (d a)
  map_one' := by
    rw [d.map_one_eq_zero, map_zero, map_one, mul_zero, add_zero]
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, mul_add]
    ring
  map_mul' a b := by
    rw [d.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, mul_add, add_mul]
    have hh : (epsilonIn k C * s (d a)) * (epsilonIn k C * s (d b)) = 0 := by
      calc
        (epsilonIn k C * s (d a)) * (epsilonIn k C * s (d b)) =
            (epsilonIn k C * epsilonIn k C) * (s (d a) * s (d b)) := by ring
        _ = 0 := by rw [epsilonIn_square, zero_mul]
    rw [hh]
    ring
  commutes' r := by
    rw [d.map_algebraMap, map_zero, mul_zero, add_zero, s.commutes]

theorem adjustSection_apply (s : B →ₐ[k] C) (d : Derivation k B B) (a : B) :
    adjustSection k C B s d a = s a + epsilonIn k C * s (d a) := by
  unfold adjustSection
  rfl

theorem adjustSection_reduce (ρ : C →ₐ[k] B) (s : B →ₐ[k] C) (d : Derivation k B B)
    (hs : ∀ a, ρ (s a) = a)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C)) (a : B) :
    ρ (adjustSection k C B s d a) = a := by
  have he : ρ (epsilonIn k C) = 0 := map_epsilon_eq_zero k C B ρ.toRingHom hker
  rw [adjustSection_apply, map_add, map_mul, he, zero_mul, add_zero, hs]

/-- Exact equality of the corrected affine splittings when the Čech difference is a coboundary. -/
theorem adjustSections_agree_of_coboundary [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →ₐ[k] B) (s₁ s₂ : B →ₐ[k] C)
    (h₁ : ∀ a, ρ (s₁ a) = a) (h₂ : ∀ a, ρ (s₂ a) = a)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C))
    (d₁ d₂ : Derivation k B B)
    (h : differenceDerivation k C B ρ s₁ s₂ h₁ h₂ hker = d₂ - d₁) :
    adjustSection k C B s₁ (-d₁) = adjustSection k C B s₂ (-d₂) := by
  apply AlgHom.ext
  intro a
  have hb := differenceDerivation_beta k C B ρ s₁ s₂ h₁ h₂ hker a
  rw [h, Derivation.sub_apply, map_sub, mul_sub] at hb
  have hc := epsilon_mul_eq_of_eq_reduction k C B ρ hker
    ((h₁ (d₂ a)).trans (h₂ (d₂ a)).symm)
  rw [adjustSection_apply k C B s₁, adjustSection_apply k C B s₂]
  simp only [Derivation.neg_apply, map_neg, mul_neg, ← sub_eq_add_neg]
  calc
    s₁ a - epsilonIn k C * s₁ (d₁ a) =
      s₁ a + (epsilonIn k C * s₁ (d₂ a) - epsilonIn k C * s₁ (d₁ a)) -
        epsilonIn k C * s₁ (d₂ a) := by ring
    _ = s₂ a - epsilonIn k C * s₂ (d₂ a) := by
      rw [hb, hc]
      ring

end Correction

end SelectedSameAAffineChartGauge318
