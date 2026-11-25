module
public import OriginalR40ActualOldChartMaps318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section

namespace OriginalUpperR40SplitOuterScalar318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318 Polynomial
open OriginalThickCentralReesChart318 (O x y)
open OriginalThickOuterReesChart318 (a b oldToOuter old_a old_b)
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R k : Type} [CommRing R] [Field k] [Algebra R k]
variable (q : R) (d : ℕ) (ε : Bool) (f : O q d →ₐ[R] k)

/-- At the old node the outer chart's first axis vanishes. The surviving
second variable is the original R40 homogeneous ratio q/a. -/
@[expose] def lineRead (hq : algebraMap R k q = 0) : Node q →ₐ[R] k[X] :=
  eval q 0 X (by
    rw [mul_zero, IsScalarTower.algebraMap_apply R k k[X], hq, map_zero])

theorem outer_commutes (hq : algebraMap R k q = 0)
    (hx : f (x q d) = 0) (hy : f (y q d) = 0) :
    (lineRead q hq).comp (oldToOuter q d ε) =
      (IsScalarTower.toAlgHom R k k[X]).comp f := by
  have ha : ((lineRead q hq).comp (oldToOuter q d ε)) (a q d ε) =
      ((IsScalarTower.toAlgHom R k k[X]).comp f) (a q d ε) := by
    rw [AlgHom.comp_apply, old_a, lineRead, eval_x]
    change 0 = algebraMap k k[X] (f (a q d ε))
    have he : f (a q d ε) = 0 := by cases ε <;> assumption
    rw [he, map_zero]
  have hb : ((lineRead q hq).comp (oldToOuter q d ε)) (b q d ε) =
      ((IsScalarTower.toAlgHom R k k[X]).comp f) (b q d ε) := by
    rw [AlgHom.comp_apply, old_b, map_mul, map_pow, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R k k[X], hq, map_zero,
      zero_pow (Nat.succ_ne_zero d), zero_mul]
    change 0 = algebraMap k k[X] (f (b q d ε))
    have he : f (b q d ε) = 0 := by cases ε <;> assumption
    rw [he, map_zero]
  cases ε
  · exact OriginalNodeRingMaps318.ext hb ha
  · exact OriginalNodeRingMaps318.ext ha hb

/-- The two actual coefficient-map algebras are local and are exactly
the maps in the original outer chart's pullback diagram. -/
@[expose] def withRead (hq : algebraMap R k q = 0)
    (hx : f (x q d) = 0) (hy : f (y q d) = 0) :
    letI : Algebra (O q d) k := f.toRingHom.toAlgebra
    letI : Algebra (O q d) (Node q) := (oldToOuter q d ε).toRingHom.toAlgebra
    { e : (k ⊗[O q d] Node q) ≃ₐ[k] k[X] //
      ∀ z : Node q, e (Algebra.TensorProduct.includeRight z) = lineRead q hq z } := by
  let A := O q d
  let P := Node q
  let C := k[X]
  let : Algebra A k := f.toRingHom.toAlgebra
  let : Algebra A P := (oldToOuter q d ε).toRingHom.toAlgebra
  let T := k ⊗[A] P
  change {e : T ≃ₐ[k] C // ∀ z : P, e (Algebra.TensorProduct.includeRight z) = lineRead q hq z}
  let : IsScalarTower R A P := IsScalarTower.of_algebraMap_eq
    (R:=R) (S:=A) (A:=P) fun z => ((oldToOuter q d ε).commutes z).symm
  let : Algebra A C := ((algebraMap k C).comp f.toRingHom).toAlgebra
  let right : P →ₐ[A] T := Algebra.TensorProduct.includeRight
  let adjusted : P →ₐ[A] C :=
    { toRingHom := (lineRead q hq).toRingHom
      commutes' := fun z => show lineRead q hq (oldToOuter q d ε z) = algebraMap k C (f z) from
        DFunLike.congr_fun (outer_commutes q d ε f hq hx hy) z }
  let left : k →ₐ[A] C := ⟨algebraMap k C, fun _ => rfl⟩
  let product : T →ₐ[A] C := Algebra.TensorProduct.productMap left adjusted
  let forward : T →ₐ[k] C :=
    ⟨product.toRingHom, fun t => by
      change product (t ⊗ₜ[A] (1 : P)) = left t
      exact Algebra.TensorProduct.productMap_left_apply left adjusted t⟩
  have fr (z : P) : forward (right z) = lineRead q hq z := by
    change product ((1 : k) ⊗ₜ[A] z) = adjusted z
    exact Algebra.TensorProduct.productMap_right_apply left adjusted z
  have rc (z : R) : right (algebraMap R P z) = algebraMap k T (algebraMap R k z) := by
    rw [IsScalarTower.algebraMap_apply R A P, right.commutes, IsScalarTower.algebraMap_apply A k T]
    change algebraMap k T (f (algebraMap R A z)) = _
    rw [f.commutes]
  let u := xAxis q
  let v := yAxis q
  have hu : right u = 0 := by
    have h : f (a q d ε) = 0 := by cases ε <;> assumption
    change right (xAxis q) = 0
    rw [← old_a q d ε]
    change right (algebraMap A P (a q d ε)) = 0
    rw [right.commutes, IsScalarTower.algebraMap_apply A k T]
    change algebraMap k T (f (a q d ε)) = 0
    rw [h, map_zero]
  let backward : C →ₐ[k] T := aeval (right v)
  have bv : backward X = right v := aeval_X _
  have fx : forward (right u) = 0 := (fr u).trans (eval_x _ _ _ _)
  have fy : forward (right v) = X := (fr v).trans (eval_y _ _ _ _)
  let : Algebra R T := ((algebraMap k T).comp (algebraMap R k)).toAlgebra
  let g₁ : P →ₐ[R] T :=
    ⟨backward.toRingHom.comp (forward.toRingHom.comp right.toRingHom), fun z => by
      change backward (forward (right (algebraMap R P z))) = algebraMap k T (algebraMap R k z)
      exact (congrArg (fun t : T => backward (forward t)) (rc z)).trans
        ((congrArg backward (forward.commutes (algebraMap R k z))).trans
          (backward.commutes (algebraMap R k z)))⟩
  let g₂ : P →ₐ[R] T := ⟨right.toRingHom, fun z => rc z⟩
  have h1 : forward.comp backward = AlgHom.id k C := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, bv, fy, AlgHom.id_apply]
  have hxyt : g₁ = g₂ := by
    apply OriginalNodeRingMaps318.ext
    · change backward (forward (right u)) = right u
      rw [fx, map_zero, hu]
    · change backward (forward (right v)) = right v
      rw [fy, bv]
  have h2 : backward.comp forward = AlgHom.id k T := by
    apply AlgHom.toRingHom_injective
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro t
      change backward (forward (algebraMap k T t)) = algebraMap k T t
      rw [forward.commutes, backward.commutes]
    · apply RingHom.ext
      intro z
      change g₁ z = g₂ z
      exact DFunLike.congr_fun hxyt z
  exact ⟨AlgEquiv.ofAlgHom forward backward h1 h2, fr⟩

@[expose] def tensor (hq : algebraMap R k q = 0)
    (hx : f (x q d) = 0) (hy : f (y q d) = 0) :
    letI : Algebra (O q d) k := f.toRingHom.toAlgebra
    letI : Algebra (O q d) (Node q) := (oldToOuter q d ε).toRingHom.toAlgebra
    (k ⊗[O q d] Node q) ≃ₐ[k] k[X] :=
  (withRead q d ε f hq hx hy).val

theorem tensor_right (hq : algebraMap R k q = 0)
    (hx : f (x q d) = 0) (hy : f (y q d) = 0) (z : Node q) :
    letI : Algebra (O q d) k := f.toRingHom.toAlgebra
    letI : Algebra (O q d) (Node q) := (oldToOuter q d ε).toRingHom.toAlgebra
    tensor q d ε f hq hx hy (Algebra.TensorProduct.includeRight z) = lineRead q hq z :=
  (withRead q d ε f hq hx hy).property z

theorem ratio_read (hq : algebraMap R k q = 0)
    (hx : f (x q d) = 0) (hy : f (y q d) = 0) :
    letI : Algebra (O q d) k := f.toRingHom.toAlgebra
    letI : Algebra (O q d) (Node q) := (oldToOuter q d ε).toRingHom.toAlgebra
    tensor q d ε f hq hx hy (Algebra.TensorProduct.includeRight (yAxis q)) = X :=
  (tensor_right q d ε f hq hx hy (yAxis q)).trans (eval_y _ _ _ _)

end OriginalUpperR40SplitOuterScalar318

#print axioms OriginalUpperR40SplitOuterScalar318.withRead
#print axioms OriginalUpperR40SplitOuterScalar318.tensor
#print axioms OriginalUpperR40SplitOuterScalar318.tensor_right
#print axioms OriginalUpperR40SplitOuterScalar318.ratio_read
