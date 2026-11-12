module
public import ActualTwoDescentFieldGaloisConnectingKernel318
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section
namespace ActualTwoDescentFieldGaloisLocallyConstant318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318
local instance : DecidableEq Qbar := Classical.decEq _

/-- Each algebraic coordinate has an OPEN stabilizer in the actual Krull topology. -/
lemma actual_galois_coordinate_locally_constant (x : Qbar) : IsLocallyConstant (fun σ : GalQ => σ x) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro σ
  let S := (MulAction.stabilizer (Qbar ≃ₐ[F] Qbar) x : Set GalQ)
  have hS : IsOpen S := stabilizer_isOpen_of_isIntegral x
  refine ⟨(fun τ : GalQ => σ⁻¹*τ) ⁻¹' S,hS.preimage (continuous_const.mul continuous_id),?_,?_⟩
  · change σ⁻¹*σ ∈ MulAction.stabilizer (Qbar ≃ₐ[F] Qbar) x
    simp only [inv_mul_cancel]
    exact (MulAction.stabilizer _ x).one_mem
  · intro τ hτ
    have he : (σ⁻¹*τ) x=x := hτ
    have h := congrArg σ he
    change σ (σ.symm (τ x))=σ x at h
    simpa only [σ.apply_symm_apply] using h

lemma actual_galois_point_locally_constant (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) :
    IsLocallyConstant (fun σ : GalQ => galoisPointHom σ n hn Q) := by
  cases Q with
  | zero => exact IsLocallyConstant.const 0
  | some x y h =>
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro σ
    obtain ⟨U,hU,hσU,hx⟩ := (IsLocallyConstant.iff_exists_open _).mp (actual_galois_coordinate_locally_constant x) σ
    obtain ⟨V,hV,hσV,hy⟩ := (IsLocallyConstant.iff_exists_open _).mp (actual_galois_coordinate_locally_constant y) σ
    refine ⟨U∩V,hU.inter hV,⟨hσU,hσV⟩,?_⟩
    intro τ hτ
    simp only [galoisPointHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,galoisPoint,point,hx τ hτ.1,hy τ hτ.2]

/-- The actual half-difference cocycle is locally constant, not just an abstract group cocycle. -/
theorem actual_halving_cocycle_locally_constant (n : F) (hn : n ≠ 0) (P : Point n) :
    IsLocallyConstant (rationalHalvingCocycle n hn P) := by
  let Q := actualHalf n hn (rationalPointMap n hn P)
  have hd : IsLocallyConstant (fun σ : GalQ => halfDifference n hn Q σ) :=
    (actual_galois_point_locally_constant n hn Q).comp (fun R => R-Q)
  apply IsLocallyConstant.desc (rationalHalvingCocycle n hn P)
    (fun T : Multiplicative (closedTwoTorsion n) => (T.toAdd : Point (algebraMap F Qbar n)))
  · exact hd
  · intro a b h
    exact Subtype.ext h

end ActualTwoDescentFieldGaloisLocallyConstant318
