module

public import SelectedSameADualNumberFlatCoefficient318
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.Ring

/-!
# A literal affine chart of the infinitesimally pulled same-A family

Flatness and the exact principal reduction give the nilpotent coefficient. Formal smoothness
then chooses the section of reduction, rather than assuming the affine product trivialization.
-/

public section

open MulOpposite

namespace SelectedSameAADualNumberAffineChart318

open SelectedSameADualNumberFlatCoefficient318

variable (k C B : Type*) [CommRing k] [CommRing C] [CommRing B]
  [Algebra (TrivSqZeroExt k k) C]

/-- Pointwise beta for the nilpotent direction of the actual reduction map. -/
theorem map_epsilon_eq_zero (ρ : C →+* B)
    (hker : RingHom.ker ρ = Ideal.span ({epsilonIn k C} : Set C)) :
    ρ (epsilonIn k C) = 0 := by
  apply RingHom.mem_ker.mp
  rw [hker]
  exact Ideal.mem_span_singleton_self _

private theorem ker_nil (ρ : C →+* B)
    (hker : RingHom.ker ρ = Ideal.span ({epsilonIn k C} : Set C)) :
    IsNilpotent (RingHom.ker ρ) := by
  refine ⟨2, ?_⟩
  rw [pow_two, hker]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hy
  rw [Ideal.mem_bot]
  calc
    (epsilonIn k C * a) * (epsilonIn k C * b) =
        (epsilonIn k C * epsilonIn k C) * (a * b) := by ring
    _ = 0 := by rw [epsilonIn_square, zero_mul]

section GivenSection

variable (s : B →+* C)

/-- The affine map on the entire dual-number chart, not just on the closed fibre. -/
def chartHom : TrivSqZeroExt B B →+* C where
  toFun x := s x.fst + epsilonIn k C * s x.snd
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add, mul_add]
    ring
  map_mul' x y := by
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul,
      smul_eq_mul, map_add, map_mul]
    simp only [add_mul, mul_add]
    have hh : (epsilonIn k C * s x.snd) * (epsilonIn k C * s y.snd) = 0 := by
      calc
        (epsilonIn k C * s x.snd) * (epsilonIn k C * s y.snd) =
          (epsilonIn k C * epsilonIn k C) * (s x.snd * s y.snd) := by ring
        _ = 0 := by rw [epsilonIn_square, zero_mul]
    rw [hh]
    ring

theorem chartHom_apply (x : TrivSqZeroExt B B) :
    chartHom k C B s x = s x.fst + epsilonIn k C * s x.snd := by
  unfold chartHom
  rfl

theorem chartHom_reduce (ρ : C →+* B) (hs : ∀ b, ρ (s b) = b)
    (hker : RingHom.ker ρ = Ideal.span ({epsilonIn k C} : Set C))
    (x : TrivSqZeroExt B B) : ρ (chartHom k C B s x) = x.fst := by
  rw [chartHom_apply, map_add, map_mul, map_epsilon_eq_zero k C B ρ hker,
    hs, zero_mul, add_zero]

private theorem chartHom_bijective [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →+* B) (hs : ∀ b, ρ (s b) = b)
    (hker : RingHom.ker ρ = Ideal.span ({epsilonIn k C} : Set C)) :
    Function.Bijective (chartHom k C B s) := by
  constructor
  · intro x y hxy
    have ha : x.fst = y.fst := by
      simpa only [chartHom_reduce k C B s ρ hs hker] using congrArg ρ hxy
    rw [chartHom_apply k C B s x, chartHom_apply k C B s y, ha] at hxy
    have hcoef : epsilonIn k C * s x.snd = epsilonIn k C * s y.snd :=
      add_left_cancel hxy
    have hz : ρ (epsilonIn k C * s y.snd) = 0 := by
      rw [map_mul, map_epsilon_eq_zero k C B ρ hker, zero_mul]
    obtain ⟨b, _, hu⟩ := existsUnique_coefficient k C ρ s hs hker _ hz
    exact TrivSqZeroExt.ext ha ((hu x.snd hcoef).trans (hu y.snd rfl).symm)
  · intro z
    have hz : ρ (z - s (ρ z)) = 0 := by rw [map_sub, hs, sub_self]
    obtain ⟨b, hb, _⟩ := existsUnique_coefficient k C ρ s hs hker _ hz
    refine ⟨(ρ z, b), ?_⟩
    rw [chartHom_apply]
    change s (ρ z) + epsilonIn k C * s b = z
    rw [hb]
    ring

/-- Product chart from a section, with the actual reduction left fixed. -/
noncomputable def chartOfSection [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →+* B) (hs : ∀ b, ρ (s b) = b)
    (hker : RingHom.ker ρ = Ideal.span ({epsilonIn k C} : Set C)) :
    TrivSqZeroExt B B ≃+* C :=
  RingEquiv.ofBijective (chartHom k C B s) (chartHom_bijective k C B s ρ hs hker)

theorem chartOfSection_apply [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →+* B) (hs : ∀ b, ρ (s b) = b)
    (hker : RingHom.ker ρ = Ideal.span ({epsilonIn k C} : Set C))
    (x : TrivSqZeroExt B B) :
    chartOfSection k C B s ρ hs hker x = s x.fst + epsilonIn k C * s x.snd := by
  unfold chartOfSection
  exact chartHom_apply k C B s x

end GivenSection

section ActualChart

variable [Algebra k C] [Algebra k B] [Algebra.FormallySmooth k B]

/-- The chosen section is a genuine lift of the identity on the same reduction. -/
noncomputable def chosenSection (ρ : C →ₐ[k] B) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C)) :
    B →ₐ[k] C :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k B) ρ hρ
    (ker_nil k C B ρ.toRingHom hker)

theorem chosenSection_reduce (ρ : C →ₐ[k] B) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C)) (b : B) :
    ρ (chosenSection k C B ρ hρ hker b) = b := by
  unfold chosenSection
  exact Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id k B) ρ hρ
    (ker_nil k C B ρ.toRingHom hker) b

/-- A trivialization of the whole affine, constructed from flatness and the smooth reduction. -/
noncomputable def actualChart [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →ₐ[k] B) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C)) :
    TrivSqZeroExt B B ≃+* C :=
  chartOfSection k C B (chosenSection k C B ρ hρ hker).toRingHom ρ.toRingHom
    (chosenSection_reduce k C B ρ hρ hker) hker

theorem actualChart_reduce [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →ₐ[k] B) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C))
    (x : TrivSqZeroExt B B) : ρ (actualChart k C B ρ hρ hker x) = x.fst := by
  let s := chosenSection k C B ρ hρ hker
  have hs := chosenSection_reduce k C B ρ hρ hker
  change ρ.toRingHom (chartOfSection k C B s.toRingHom ρ.toRingHom hs hker x) = x.fst
  rw [chartOfSection_apply, map_add, map_mul, map_epsilon_eq_zero k C B ρ.toRingHom hker,
    zero_mul, add_zero]
  exact hs x.fst

theorem actualChart_epsilon [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →ₐ[k] B) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C)) :
    actualChart k C B ρ hρ hker (TrivSqZeroExt.inr 1) = epsilonIn k C := by
  unfold actualChart
  rw [chartOfSection_apply]
  simp

/-- The chart maps the constants of the fixed residue field to the same constants. -/
theorem actualChart_constants [Module.Flat (TrivSqZeroExt k k) C]
    (ρ : C →ₐ[k] B) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C)) (r : k) :
    actualChart k C B ρ hρ hker (TrivSqZeroExt.inl (algebraMap k B r)) =
      algebraMap k C r := by
  unfold actualChart
  rw [chartOfSection_apply]
  simp only [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, map_zero, mul_zero, add_zero]
  exact (chosenSection k C B ρ hρ hker).commutes r

end ActualChart

end SelectedSameAADualNumberAffineChart318
