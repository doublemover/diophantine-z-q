module
public import OriginalR40ActualOldChartMaps318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section

namespace OriginalUpperR40SplitCentralScalar318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalThickCentralReesChart318 (O x y oldToNew)
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R k : Type} [CommRing R] [Field k] [Algebra R k]
variable (q : R) (d : ℕ) (f : O q d →ₐ[R] k)

abbrev cbar := algebraMap R k (q^d)
abbrev oldCentral := Node (q^d)
abbrev newCentral := Node (cbar (k:=k) q d)

/-- Map the literal central coordinates to the exact changed coefficient. -/
@[expose] def scalarNode : oldCentral q d →ₐ[R] newCentral (k:=k) q d :=
  eval (q^d) (xAxis (cbar q d)) (yAxis (cbar q d)) (by
    rw [node_relation]
    exact (IsScalarTower.algebraMap_apply R k (newCentral q d) (q^d)).symm)

theorem central_commutes (hq : algebraMap R k q = 0)
    (hx : f (x q d) = 0) (hy : f (y q d) = 0) :
    (scalarNode (k:=k) q d).comp (oldToNew q d) =
      (IsScalarTower.toAlgHom R k (newCentral q d)).comp f := by
  apply OriginalNodeRingMaps318.ext
  · change scalarNode q d (oldToNew q d (x q d)) = algebraMap k _ (f (x q d))
    rw [oldToNew, eval_x, map_mul, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R k (newCentral q d), hq, map_zero, zero_mul, hx, map_zero]
  · change scalarNode q d (oldToNew q d (y q d)) = algebraMap k _ (f (y q d))
    rw [oldToNew, eval_y, map_mul, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R k (newCentral q d), hq, map_zero, zero_mul, hy, map_zero]

/-- Both algebra structures are installed by the named actual maps, and
the right coordinate inclusion is retained in the same certificate. -/
@[expose] def withRead (hq : algebraMap R k q = 0)
    (hx : f (x q d) = 0) (hy : f (y q d) = 0) :
    letI : Algebra (O q d) k := f.toRingHom.toAlgebra
    letI : Algebra (O q d) (oldCentral q d) := (oldToNew q d).toRingHom.toAlgebra
    { e : (k ⊗[O q d] oldCentral q d) ≃ₐ[k] newCentral (k:=k) q d //
      ∀ z : oldCentral q d, e (Algebra.TensorProduct.includeRight z) = scalarNode q d z } := by
  let A := O q d
  let P := oldCentral q d
  let C := newCentral (k:=k) q d
  let : Algebra A k := f.toRingHom.toAlgebra
  let : Algebra A P := (oldToNew q d).toRingHom.toAlgebra
  let T := k ⊗[A] P
  change {e : T ≃ₐ[k] C // ∀ z : P, e (Algebra.TensorProduct.includeRight z) = scalarNode q d z}
  let : IsScalarTower R A P := IsScalarTower.of_algebraMap_eq
    (R:=R) (S:=A) (A:=P) fun z => ((oldToNew q d).commutes z).symm
  let : Algebra A C := ((algebraMap k C).comp f.toRingHom).toAlgebra
  let right : P →ₐ[A] T := Algebra.TensorProduct.includeRight
  let adjusted : P →ₐ[A] C :=
    { toRingHom := (scalarNode (k:=k) q d).toRingHom
      commutes' := fun z => show scalarNode q d (oldToNew q d z) = algebraMap k C (f z) from
        DFunLike.congr_fun (central_commutes q d f hq hx hy) z }
  let left : k →ₐ[A] C := ⟨algebraMap k C, fun _ => rfl⟩
  let product : T →ₐ[A] C := Algebra.TensorProduct.productMap left adjusted
  let forward : T →ₐ[k] C :=
    ⟨product.toRingHom, fun t => by
      change product (t ⊗ₜ[A] (1 : P)) = left t
      exact Algebra.TensorProduct.productMap_left_apply left adjusted t⟩
  have fr (z : P) : forward (right z) = scalarNode q d z := by
    change product ((1 : k) ⊗ₜ[A] z) = adjusted z
    exact Algebra.TensorProduct.productMap_right_apply left adjusted z
  have rc (z : R) : right (algebraMap R P z) = algebraMap k T (algebraMap R k z) := by
    rw [IsScalarTower.algebraMap_apply R A P, right.commutes, IsScalarTower.algebraMap_apply A k T]
    change algebraMap k T (f (algebraMap R A z)) = _
    rw [f.commutes]
  let u := xAxis (q^d)
  let v := yAxis (q^d)
  have hr : right v * right u = algebraMap k T (cbar (k:=k) q d) := by
    rw [← map_mul]
    change right (yAxis (q^d) * xAxis (q^d)) = _
    rw [node_relation]
    exact rc (q^d)
  let backward : C →ₐ[k] T := eval (cbar q d) (right u) (right v) hr
  have bx : backward (xAxis (cbar q d)) = right u := eval_x _ _ _ _
  have byy : backward (yAxis (cbar q d)) = right v := eval_y _ _ _ _
  have fx : forward (right u) = xAxis (cbar q d) := (fr u).trans (eval_x _ _ _ _)
  have fy : forward (right v) = yAxis (cbar q d) := (fr v).trans (eval_y _ _ _ _)
  let : Algebra R T := ((algebraMap k T).comp (algebraMap R k)).toAlgebra
  let g₁ : P →ₐ[R] T :=
    ⟨backward.toRingHom.comp (forward.toRingHom.comp right.toRingHom), fun z => by
      change backward (forward (right (algebraMap R P z))) = algebraMap k T (algebraMap R k z)
      exact (congrArg (fun t : T => backward (forward t)) (rc z)).trans
        ((congrArg backward (forward.commutes (algebraMap R k z))).trans
          (backward.commutes (algebraMap R k z)))⟩
  let g₂ : P →ₐ[R] T := ⟨right.toRingHom, fun z => rc z⟩
  have h1 : forward.comp backward = AlgHom.id k C := by
    apply OriginalNodeRingMaps318.ext
    · rw [AlgHom.comp_apply, bx, fx, AlgHom.id_apply]
    · rw [AlgHom.comp_apply, byy, fy, AlgHom.id_apply]
  have hxyt : g₁ = g₂ := by
    apply OriginalNodeRingMaps318.ext
    · change backward (forward (right u)) = right u
      rw [fx, bx]
    · change backward (forward (right v)) = right v
      rw [fy, byy]
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
    letI : Algebra (O q d) (oldCentral q d) := (oldToNew q d).toRingHom.toAlgebra
    (k ⊗[O q d] oldCentral q d) ≃ₐ[k] newCentral (k:=k) q d :=
  (withRead q d f hq hx hy).val

theorem cbar_eq (hq : algebraMap R k q = 0) :
    cbar (k:=k) q d = if d = 0 then (1 : k) else 0 := by
  by_cases hd : d = 0
  · subst d
    simp
  · rw [cbar, map_pow, hq, zero_pow hd, ite_eq_right hd]

end OriginalUpperR40SplitCentralScalar318

#print axioms OriginalUpperR40SplitCentralScalar318.withRead
#print axioms OriginalUpperR40SplitCentralScalar318.tensor
#print axioms OriginalUpperR40SplitCentralScalar318.cbar_eq
