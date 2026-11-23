module
public import SelectedActualSameAFiniteDlogRows318
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import all SelectedActualSameAFiniteDlogRows318

/-! The integer dlog rows as explicit coefficients in a given finite-place
integer ring. The chart map, transported product rule and frame multiplier
are inputs; this does not construct or specialize an original structural DVR. -/
public section
noncomputable section

open NumberField SelectedActualSameAFiniteDlogRows318

namespace SelectedActualSameAFiniteMappedDlogRows318

theorem map_row0 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (d : Fin 4 → R) : f (row0 d) = row0 (fun i => f (d i)) := by
  simp only [row0, map_sub, map_add, map_mul, map_ofNat]

theorem map_row1 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (d : Fin 4 → R) : f (row1 d) = row1 (fun i => f (d i)) := by
  simp only [row1, map_sub, map_add, map_mul, map_neg, map_ofNat]

variable {F : Type*} [Field F] [NumberField F]

abbrev PlaceIntegers (w : FinitePlace F) := (w.maximalIdeal.valuation F).integer

private theorem bounded_iff (w : FinitePlace F) (x : F) :
    w x ≤ 1 ↔ w.maximalIdeal.valuation F x ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq w x, FinitePlace.norm_embedding']
  exact_mod_cast WithZeroMulInt.toNNReal_le_one_iff
    (HeightOneSpectrum.one_lt_absNorm_nnreal w.maximalIdeal)

/-- Apply the given chart map to the actual integer rows before reading them
in the fraction field. The multiplier is already integral in this frame. -/
@[expose] def mappedRows {R : Type*} [CommRing R] (w : FinitePlace F)
    (φ : R →+* PlaceIntegers w) (d : Fin 4 → R) (u : PlaceIntegers w) :
    Fin 2 → PlaceIntegers w :=
  ![u * φ (row0 d), u * φ (row1 d)]

/-- The two ordered coefficients are integral by construction and have the
literal field read when the given chart data satisfy the four dlog equations
there. No denominators are divided inside the valuation integer ring. -/
theorem mappedRows_read_bounded {R : Type*} [CommRing R] (w : FinitePlace F)
    (φ : R →+* PlaceIntegers w) (d : Fin 4 → R) (u : PlaceIntegers w) (t dt : F)
    (hn : ∀ k, contact t k ≠ 0)
    (h : ∀ k, dt = 2 * contact t k * algebraMap (PlaceIntegers w) F (φ (d k)))
    (i : Fin 2) :
    algebraMap (PlaceIntegers w) F (mappedRows w φ d u i) =
        algebraMap (PlaceIntegers w) F u *
          ((25725 / 4 : F) * (![32, t] : Fin 2 → F) i * qcoeff t dt) ∧
      w (algebraMap (PlaceIntegers w) F (mappedRows w φ d u i)) ≤ 1 := by
  let j : PlaceIntegers w →+* F := algebraMap (PlaceIntegers w) F
  let g : R →+* F := j.comp φ
  have hh : ∀ k, dt = 2 * contact t k * g (d k) := by
    intro k
    change dt = 2 * contact t k * (j.comp φ) (d k)
    rw [RingHom.comp_apply]
    exact h k
  have hr := read_rows t dt (fun k => g (d k)) hn hh
  refine ⟨?_, (bounded_iff w _).mpr
    ((Valuation.integer.integers (w.maximalIdeal.valuation F)).map_le_one
      (mappedRows w φ d u i))⟩
  fin_cases i
  · change j (u * φ (row0 d)) = j u * ((25725 / 4 : F) * 32 * qcoeff t dt)
    calc
      _ = j u * j (φ (row0 d)) := map_mul _ _ _
      _ = j u * g (row0 d) :=
        congrArg (fun x : F => j u * x) (RingHom.comp_apply j φ (row0 d)).symm
      _ = _ := congrArg (fun x : F => j u * x) ((map_row0 g d).trans hr.1)
  · change j (u * φ (row1 d)) = j u * ((25725 / 4 : F) * t * qcoeff t dt)
    calc
      _ = j u * j (φ (row1 d)) := map_mul _ _ _
      _ = j u * g (row1 d) :=
        congrArg (fun x : F => j u * x) (RingHom.comp_apply j φ (row1 d)).symm
      _ = _ := congrArg (fun x : F => j u * x) ((map_row1 g d).trans hr.2)

end SelectedActualSameAFiniteMappedDlogRows318
