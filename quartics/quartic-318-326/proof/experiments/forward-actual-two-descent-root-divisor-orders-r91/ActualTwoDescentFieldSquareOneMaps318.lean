module
public import ActualTwoDescentFieldSquareOneUnits318
public section
noncomputable section
namespace ActualTwoDescentFieldSquareOneMaps318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldSquareOneUnits318
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

def squareOneMap (f : K →+* L) : SquareOne K →* SquareOne L where
  toFun u := ⟨Units.map f.toMonoidHom u,by
    change (Units.map f.toMonoidHom (u : Kˣ))^2=1
    rw [←map_pow]
    have h : (u : Kˣ)^2=1 := u.property
    rw [h,map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ _ _)

lemma actual_square_one_map_injective (f : K →+* L) : Function.Injective (squareOneMap f) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  apply f.injective
  exact congrArg (fun w : SquareOne L => ((w : Lˣ) : L)) h

lemma actual_square_one_map_surjective (f : K →+* L) : Function.Surjective (squareOneMap f) := by
  intro u
  rcases actual_square_one_cases u with rfl|rfl
  · exact ⟨1,(squareOneMap f).map_one⟩
  · refine ⟨negativeOne,?_⟩
    apply Subtype.ext
    apply Units.ext
    change f (-1)= -1
    rw [map_neg,map_one]

def squareOneMapEquiv (f : K →+* L) : SquareOne K ≃* SquareOne L :=
  MulEquiv.ofBijective (squareOneMap f) ⟨actual_square_one_map_injective f,actual_square_one_map_surjective f⟩

end ActualTwoDescentFieldSquareOneMaps318
