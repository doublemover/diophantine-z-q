module
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.FieldTheory.AbsoluteGaloisGroup
public section
noncomputable section

namespace CTActualKrullCoordinateOrbit318

variable {F : Type} [Field F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

/-- Each algebraic coordinate has an OPEN stabilizer in the actual Krull topology. -/
lemma field_coordinate_locally_constant (x : Qbar) : IsLocallyConstant (fun σ : GalQ =>
    (show Qbar ≃ₐ[F] Qbar from σ) x) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro σ
  let H : Subgroup (Qbar ≃ₐ[F] Qbar) := MulAction.stabilizer (Qbar ≃ₐ[F] Qbar) x
  let C : Set (Qbar ≃ₐ[F] Qbar) := ↑H
  let S : Set GalQ := C
  have hC : IsOpen C := stabilizer_isOpen_of_isIntegral x
  have hS : IsOpen S := by
    change IsOpen C
    exact hC
  refine ⟨(fun τ : GalQ => σ⁻¹*τ) ⁻¹' S,hS.preimage (continuous_const.mul continuous_id),?_,?_⟩
  · let s : Qbar ≃ₐ[F] Qbar := σ
    change s⁻¹*s ∈ H
    simpa only [inv_mul_cancel] using H.one_mem
  · intro τ hτ
    let s : Qbar ≃ₐ[F] Qbar := σ
    let t : Qbar ≃ₐ[F] Qbar := τ
    have hmem : s⁻¹*t ∈ H := by
      change s⁻¹*t ∈ H at hτ
      exact hτ
    have he : (s⁻¹*t) x = x := hmem
    have h : s (s.symm (t x)) = s x := congrArg s he
    change t x = s x
    simpa only [s.apply_symm_apply] using h

end CTActualKrullCoordinateOrbit318
