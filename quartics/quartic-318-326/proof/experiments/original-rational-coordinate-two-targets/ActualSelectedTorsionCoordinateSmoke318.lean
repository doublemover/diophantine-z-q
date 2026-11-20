module
public import ActualTwoDescentGaloisFixedRational318
import all ActualTwoDescentActualEllipticFieldMap318
import all ActualTwoDescentEllipticModel318
import all ActualTwoDescentGaloisFixedRational318
public section
noncomputable section

namespace ActualSelectedTorsionCoordinateSmoke318
open ActualTwoDescentEllipticModel318 ActualTwoDescentActualEllipticFieldMap318
open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentGaloisPointAction318
open ActualTwoDescentGaloisFixedRational318

local instance : DecidableEq Qbar := Classical.decEq _

/-- Descend the exact fixed geometric point, with the same torsion relation. -/
theorem rational_fixed_torsion_preimage (n : ℚ) (hn : n ≠ 0) (m : ℕ)
    (P : Point (algebraMap ℚ Qbar n))
    (hfix : ∀ σ : GalQ, galoisPointHom σ n hn P = P) (hP : m • P = 0) :
    ∃! R : Point n, rationalPointMap n hn R = P ∧ m • R = 0 := by
  have hinj : Function.Injective (rationalPointMap n hn) :=
    actual_elliptic_field_map_injective (algebraMap ℚ Qbar) n hn
  obtain ⟨R, hR⟩ := actual_fixed_point_rational n hn P hfix
  refine ⟨R, ⟨hR, ?_⟩, ?_⟩
  · apply hinj
    rw [map_nsmul, hR, hP, map_zero]
  · intro R' hR'
    exact hinj (hR'.1.trans hR.symm)

/-- Actual right affine root, not the identity. This exercises both original
coordinate maps and the inherited Galois/descent path on exact order two. -/
theorem rational_right_root_smoke (n : ℚ) (hn : n ≠ 0) :
    ∃! R : Point n,
      rationalPointMap n hn R =
        point (algebraMap ℚ Qbar n) (algebraMap ℚ Qbar n) 0
          (rational_parameter_ne n hn) (by ring) ∧
      (2 : ℕ) • R = 0 ∧ R ≠ 0 := by
  let R : Point n := point n n 0 hn (by ring)
  let P : Point (algebraMap ℚ Qbar n) :=
    point (algebraMap ℚ Qbar n) (algebraMap ℚ Qbar n) 0 (rational_parameter_ne n hn) (by ring)
  have hRmap : rationalPointMap n hn R = P := by
    simp only [R, P, rationalPointMap, ellipticFieldMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      pointMap, point, map_zero]
  have hR₂ : (2 : ℕ) • R = 0 := by
    rw [two_nsmul]
    dsimp only [R, point]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    rw [curve_negY]
    ring
  have hR₀ : R ≠ 0 := point_ne_zero n n 0 hn _
  have hfix (σ : GalQ) : galoisPointHom σ n hn P = P := by
    rw [← hRmap]
    exact actual_rational_point_fixed σ n hn R
  have hP₂ : (2 : ℕ) • P = 0 := by
    rw [← hRmap, ← map_nsmul, hR₂, map_zero]
  obtain ⟨S, hS, hunique⟩ := rational_fixed_torsion_preimage n hn 2 P hfix hP₂
  have hRS : R = S := hunique R ⟨hRmap, hR₂⟩
  refine ⟨S, ⟨hS.1, hS.2, hRS ▸ hR₀⟩, ?_⟩
  intro T hT
  exact hunique T ⟨hT.1, hT.2.1⟩

end ActualSelectedTorsionCoordinateSmoke318
