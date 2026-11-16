module
public import NormalizedStructureTrace318

public section
noncomputable section
namespace StructureRationalScalar318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open StructureAdditiveSheaf318 NormalizedStructureTrace318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℚ))

/-- Multiplication on the actual structure sheaf by the original structural rational section. -/
@[expose] def multiply (a : ℚ) : sheaf X ⟶ sheaf X :=
  ⟨{ app U := AddCommGrpCat.ofHom {
       toFun s := scalar p U.unop a * (show Γ(X,U.unop) from s)
       map_zero' := mul_zero _
       map_add' s t := mul_add _ _ _ }
     naturality U V j := by
       ext s
       change scalar p V.unop a * X.presheaf.map j (show Γ(X,U.unop) from s) =
         X.presheaf.map j (scalar p U.unop a * (show Γ(X,U.unop) from s))
       exact (congrArg (fun q : Γ(X,V.unop) => q * X.presheaf.map j (show Γ(X,U.unop) from s))
         (scalar_restrict p j.unop a).symm).trans
           ((X.presheaf.map j).hom.map_mul _ _).symm }⟩

theorem multiply_component (a : ℚ) (U : X.Opens) (s : Γ(X,U)) :
    (multiply p a).hom.app (op U) s = scalar p U a * s := rfl

theorem multiply_zero : multiply p 0 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change scalar p U.unop 0 * (show Γ(X,U.unop) from s) = 0
  rw [map_zero,zero_mul]

theorem multiply_one : multiply p 1 = 𝟙 _ := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change scalar p U.unop 1 * (show Γ(X,U.unop) from s) = s
  rw [map_one,one_mul]

theorem multiply_add (a b : ℚ) : multiply p (a+b) = multiply p a + multiply p b := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change scalar p U.unop (a+b) * (show Γ(X,U.unop) from s) =
    scalar p U.unop a * (show Γ(X,U.unop) from s) + scalar p U.unop b * (show Γ(X,U.unop) from s)
  rw [map_add,add_mul]

theorem multiply_mul (a b : ℚ) : multiply p (a*b) = multiply p b ≫ multiply p a := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change scalar p U.unop (a*b) * (show Γ(X,U.unop) from s) =
    scalar p U.unop a * (scalar p U.unop b * (show Γ(X,U.unop) from s))
  rw [map_mul,mul_assoc]

end StructureRationalScalar318
