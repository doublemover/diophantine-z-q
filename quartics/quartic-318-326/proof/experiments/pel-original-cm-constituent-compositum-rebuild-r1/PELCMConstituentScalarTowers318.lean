module
public import PELCMConstituentNativeOrderEmbeddings318
public import Mathlib.FieldTheory.Tower
public section
noncomputable section
namespace PELCMConstituentScalarTowers318
open PELCMQuadraticConstituentFields318 PELCMConstituentFieldEmbeddings318
open PELOriginalCM210RadicalTower318
instance constituentAlgebra (i : Fin 4) : Algebra (Field i) H :=
  (embedding i).toRingHom.toAlgebra
instance constituentTower (i : Fin 4) : IsScalarTower ℚ (Field i) H :=
  IsScalarTower.of_algebraMap_eq (fun q => ((embedding i).commutes q).symm)
lemma algebraMap_eq_embedding (i : Fin 4) (z : Field i) :
    algebraMap (Field i) H z = embedding i z := rfl
lemma constituent_degree (i : Fin 4) : Module.finrank ℚ (Field i) = 2 :=
  QuadraticAlgebra.finrank_eq_two
lemma relative_degree (i : Fin 4) : Module.finrank (Field i) H = 8 := by
  letI : FiniteDimensional (Field i) H := FiniteDimensional.right ℚ (Field i) H
  have ht := Module.finrank_mul_finrank ℚ (Field i) H
  rw [constituent_degree, degree_sixteen] at ht
  omega
end PELCMConstituentScalarTowers318
