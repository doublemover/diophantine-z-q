module
public import ActualTwoDescentFieldScalarConnectingKernel318
public section
noncomputable section
namespace ActualTwoDescentFieldSurjectiveCharacterFactor318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

variable {G H A : Type*} [Group G] [Group H] [CommGroup A]

lemma actual_factor_values (f : G →* H) (χ : G →* A) (hk : f.ker ≤ χ.ker)
    (g h : G) (he : f g=f h) : χ g=χ h := by
  have hdiv : g/h ∈ f.ker := by change f (g/h)=1; rw [map_div,he,div_self]
  have hv : χ (g/h)=1 := hk hdiv
  rw [map_div] at hv
  exact div_eq_one.mp hv

def surjectiveCharacterFactor (f : G →* H) (hf : Function.Surjective f) (χ : G →* A) (hk : f.ker ≤ χ.ker) : H →* A where
  toFun y := χ (Classical.choose (hf y))
  map_one' := by
    have he := actual_factor_values f χ hk (Classical.choose (hf 1)) 1
      ((Classical.choose_spec (hf 1)).trans f.map_one.symm)
    exact he.trans χ.map_one
  map_mul' x y := by
    have he := actual_factor_values f χ hk (Classical.choose (hf (x*y)))
      (Classical.choose (hf x)*Classical.choose (hf y)) (by
        rw [Classical.choose_spec (hf (x*y)),map_mul,Classical.choose_spec (hf x),Classical.choose_spec (hf y)])
    exact he.trans (χ.map_mul _ _)

lemma actual_surjective_factor_value (f : G →* H) (hf : Function.Surjective f) (χ : G →* A) (hk : f.ker ≤ χ.ker) (g : G) :
    surjectiveCharacterFactor f hf χ hk (f g)=χ g :=
  actual_factor_values f χ hk _ g (Classical.choose_spec (hf (f g)))

end ActualTwoDescentFieldSurjectiveCharacterFactor318
