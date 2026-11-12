module
public import ActualTwoDescentScalarSquareRoots318
public section
noncomputable section
namespace ActualTwoDescentScalarRootCharacters318
set_option maxHeartbeats 16000000

open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentScalarSquareRoots318 ActualTwoDescentGaloisLocallyConstant318

lemma actual_root_ratio_mul (a : ℚˣ) (r : Qbar) (hr : r ≠ 0)
    (hs : r^2=algebraMap ℚ Qbar (a : ℚ)) (σ τ : GalQ) :
    rootRatio a r hr hs (σ*τ)=rootRatio a r hr hs σ*rootRatio a r hr hs τ := by
  apply Subtype.ext
  apply Units.ext
  change σ (τ r)/r=(σ r/r)*(τ r/r)
  have hfix := actual_square_one_aut_fixed σ (rootRatio a r hr hs τ)
  change σ (τ r/r)=τ r/r at hfix
  rw [map_div] at hfix
  have hσr : σ r ≠ 0 := ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero σ.toRingHom hr
  field_simp [hr,hσr] at hfix ⊢
  <;> linear_combination hfix

def rootCharacter (a : ℚˣ) (r : Qbar) (hr : r ≠ 0) (hs : r^2=algebraMap ℚ Qbar (a : ℚ)) : GalQ →* SquareOne Qbar where
  toFun := rootRatio a r hr hs
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change r/r=1
    exact div_self hr
  map_mul' := actual_root_ratio_mul a r hr hs

lemma actual_root_character_locally_constant (a : ℚˣ) (r : Qbar) (hr : r ≠ 0)
    (hs : r^2=algebraMap ℚ Qbar (a : ℚ)) : IsLocallyConstant (rootCharacter a r hr hs) := by
  apply IsLocallyConstant.desc (rootCharacter a r hr hs) (fun u : SquareOne Qbar => ((u : Qbarˣ) : Qbar))
  · exact (actual_galois_coordinate_locally_constant r).comp (fun x => x/r)
  · intro u v h
    exact Subtype.ext (Units.ext h)

def scalarCharacter (a : ℚˣ) : GalQ →* SquareOne Qbar :=
  rootCharacter a (scalarRoot a) (scalar_root_ne a) (scalar_root_square a)

end ActualTwoDescentScalarRootCharacters318
