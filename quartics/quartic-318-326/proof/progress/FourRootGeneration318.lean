module
public import FourRootAutomorphisms318
public import Mathlib.FieldTheory.IntermediateField.Basic
public section
noncomputable section
namespace FourRootGeneration318
open scoped TensorProduct
open QuadraticPresentation318 KummerTensorField318
set_option maxHeartbeats 800000
variable {F:Type*} [Field F] [CharZero F]
variable {A B C:Type*} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra F A] [Algebra F B] [Algebra F C]

theorem root_range_mem (a:F) (f:RootRing a→ₐ[F]A) (S:Subalgebra F A)
    (h:f (AdjoinRoot.root (polynomial a))∈S) (x:RootRing a) : f x∈S := by
  have ht:Algebra.adjoin F ({AdjoinRoot.root (polynomial a)}:Set (RootRing a))≤S.comap f :=
    Algebra.adjoin_le (by
      intro y hy
      have he:y=AdjoinRoot.root (polynomial a):=Set.mem_singleton_iff.mp hy
      subst y
      exact h)
  rw [AdjoinRoot.adjoinRoot_eq_top] at ht
  exact ht (by trivial)

theorem tensor_range_mem (f:A⊗[F]B→ₐ[F]C) (S:Subalgebra F C)
    (hA:∀x:A,f (x⊗ₜ[F](1:B))∈S) (hB:∀y:B,f ((1:A)⊗ₜ[F]y)∈S)
    (z:A⊗[F]B) : f z∈S := by
  induction z with
  | tmul x y =>
    have he:x⊗ₜ[F]y=(x⊗ₜ[F](1:B))*((1:A)⊗ₜ[F]y) := by simp
    rw [he,map_mul]
    exact S.mul_mem (hA x) (hB y)
  | add x y hx hy => simpa only [map_add] using S.add_mem hx hy

variable (a:Fin 4→F)
abbrev P01:=RootRing (a 0)⊗[F]RootRing (a 1)
abbrev P23:=RootRing (a 2)⊗[F]RootRing (a 3)
@[expose] def left : P01 a→ₐ[F]Raw a:=Algebra.TensorProduct.includeLeft
@[expose] def right : P23 a→ₐ[F]Raw a:=Algebra.TensorProduct.includeRight
@[expose] def factor : (i:Fin 4)→RootRing (a i)→ₐ[F]Raw a :=
  Fin.cases ((left a).comp Algebra.TensorProduct.includeLeft)
    (Fin.cases ((left a).comp Algebra.TensorProduct.includeRight)
      (Fin.cases ((right a).comp Algebra.TensorProduct.includeLeft)
        (Fin.cases ((right a).comp Algebra.TensorProduct.includeRight) (fun i=>Fin.elim0 i))))

theorem factor_root (i:Fin 4) : factor a i (AdjoinRoot.root (polynomial (a i)))=
    FourRootAutomorphisms318.generator a i := by
  fin_cases i <;> rfl

/-- The four actual tensor roots generate the entire algebra over its
original rational-function base. -/
theorem subalgebra_eq_top (S:Subalgebra F (Raw a))
    (h:∀i,FourRootAutomorphisms318.generator a i∈S) : S=⊤ := by
  apply Algebra.eq_top_iff.mpr
  intro z
  have hfactor (i:Fin 4) (x:RootRing (a i)) : factor a i x∈S :=
    root_range_mem _ _ S (by rw [factor_root];exact h i) x
  have hl (x:P01 a) : left a x∈S :=
    tensor_range_mem (left a) S (hfactor 0) (hfactor 1) x
  have hr (x:P23 a) : right a x∈S :=
    tensor_range_mem (right a) S (hfactor 2) (hfactor 3) x
  exact tensor_range_mem (AlgHom.id F (Raw a)) S hl hr z
end FourRootGeneration318
