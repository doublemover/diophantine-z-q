module
public import ActualTwoDescentFieldFiniteCharacterHilbert318
public section
noncomputable section
namespace ActualTwoDescentFieldGlobalCharacterEigenvector318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentFieldSquareOneMaps318 ActualTwoDescentFieldScalarConnectingHom318
open ActualTwoDescentFieldFiniteCharacterFactor318 ActualTwoDescentFieldFiniteCharacterHilbert318

/-- An ACTUAL algebraic eigenvector for every locally constant sign character. -/
theorem actual_global_character_eigenvector (χ : (continuousCharacters (F:=F))) :
    ∃ r : Qbar, r ≠ 0 ∧ ∀ σ : GalQ, σ r/r=(((χ : GalQ →* SquareOne Qbar) σ : Qbarˣ) : Qbar) := by
  obtain ⟨L,hf,hN,ψ,hψ⟩ := actual_finite_character_factor χ
  letI := hf
  letI := hN
  let e : SquareOne L ≃* SquareOne Qbar := squareOneMapEquiv (algebraMap L Qbar)
  let ψL : (L ≃ₐ[F] L) →* SquareOne L := e.symm.toMonoidHom.comp ψ
  obtain ⟨b,hb⟩ := actual_finite_character_hilbert ψL
  let r : Qbar := algebraMap L Qbar (b : L)
  have hr : r ≠ 0 := ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero (algebraMap L Qbar) b.ne_zero
  refine ⟨r,hr,?_⟩
  intro σ
  calc
    σ r/r=algebraMap L Qbar ((σ.restrictNormal L) (b : L)/(b : L)) := by
      rw [map_div,σ.restrictNormal_commutes L]
    _=algebraMap L Qbar ((ψL (σ.restrictNormal L) : Lˣ) : L) := congrArg (algebraMap L Qbar) (hb (σ.restrictNormal L))
    _=((ψ (σ.restrictNormal L) : Qbarˣ) : Qbar) := by
      exact congrArg (fun u : SquareOne Qbar => ((u : Qbarˣ) : Qbar)) (e.apply_symm_apply (ψ (σ.restrictNormal L)))
    _=(((χ : GalQ →* SquareOne Qbar) σ : Qbarˣ) : Qbar) :=
      congrArg (fun u : SquareOne Qbar => ((u : Qbarˣ) : Qbar)) (hψ σ)

end ActualTwoDescentFieldGlobalCharacterEigenvector318
