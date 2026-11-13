module
public import Mathlib.RingTheory.Localization.Integral
public section
noncomputable section
namespace IntegralClosureLocalizationMap318
variable {P Q B : Type*} [CommRing P] [CommRing Q] [CommRing B]
  [Algebra P Q] [Algebra P B] [Algebra Q B] [IsScalarTower P Q B]
local notation "N" => integralClosure P B
local notation "O" => integralClosure Q B

/-- The actual inclusion of normal orders inside the SAME ambient ring. -/
@[expose] def inclusion : N →ₐ[P] O where
  toFun z := ⟨z.val,z.property.tower_top⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[instance_reducible] def normalAlgebra : Algebra N O := inclusion.toRingHom.toAlgebra

lemma inclusion_value (z : N) : (inclusion z : B)=z.val := rfl
lemma inclusion_injective : Function.Injective (inclusion (P:=P) (Q:=Q) (B:=B)) := by
  intro x y h
  exact Subtype.ext (congrArg Subtype.val h)

local instance : Algebra N O := normalAlgebra
@[instance_reducible] def baseTower : IsScalarTower P N O :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
@[instance_reducible] def ambientTower : IsScalarTower N O B :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

lemma scalar_square (p : P) :
    inclusion (algebraMap P N p)=algebraMap Q O (algebraMap P Q p) := by
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply P Q B p
end IntegralClosureLocalizationMap318
