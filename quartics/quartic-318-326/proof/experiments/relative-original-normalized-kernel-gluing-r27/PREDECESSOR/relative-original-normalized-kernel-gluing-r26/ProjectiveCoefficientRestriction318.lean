module
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import OriginalAffineLineDualFrame318
public section
noncomputable section
namespace ProjectiveCoefficientRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
universe u v w
variable (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
  (M : Type w) [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]

/-- Restriction of a finite projective B-module along an R-free
algebra remains projective, using its ACTUAL finite retract maps. -/
theorem projective [Module.Free R B] [Module.Finite B M] [Module.Projective B M] :
    Module.Projective R M := by
  obtain ⟨n,f,g,_,_,h⟩ := Module.Finite.exists_comp_eq_id_of_projective B M
  letI : Module.Projective R (Fin n → B) := inferInstance
  exact Module.Projective.of_split (g.restrictScalars R) (f.restrictScalars R) (by
    ext x
    exact LinearMap.congr_fun h x)

end ProjectiveCoefficientRestriction318

namespace ProjectiveCoefficientRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
section Original
variable (R B : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ B]
  (L : Line (Spec (CommRingCat.of (R ⊗[ℚ] B))))
local instance : Module R (OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] B)) L) :=
  Module.compHom _ (algebraMap R (R ⊗[ℚ] B))
local instance : IsScalarTower R (R ⊗[ℚ] B)
    (OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] B)) L) :=
  IsScalarTower.of_compHom ..

/-- Every original affine line on every original coefficient-tensor
chart has a projective coefficient section module. This is NOT a claim
of finite generation over R: the whole affine chart is infinite over R. -/
theorem original_sections : Module.Projective R
    (OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] B)) L) := by
  letI : Module.Free R (R ⊗[ℚ] B) :=
    Module.Free.of_basis ((Module.Free.chooseBasis ℚ B).baseChange R)
  letI := (OriginalLineAffineModel318.properties (CommRingCat.of (R ⊗[ℚ] B)) L).1
  exact projective R (R ⊗[ℚ] B) _
end Original
end ProjectiveCoefficientRestriction318
