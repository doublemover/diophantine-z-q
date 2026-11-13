module
public import IntegralZoomBaseChange318
public import FieldQuadraticZoomEquiv318
public section
noncomputable section
namespace IntegralZoomGenericOpen318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {V K : Type*} [CommRing V] [Field K] [CharZero K] [Algebra V K]
  (α β γ : Fin 4 → V) (t : V) (y : Fin 4 → V)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value α β γ t i)
  (hn : ∀ i,algebraMap V K (y i)≠0)
abbrev mapped (a : Fin 4 → V) := fun i => algebraMap V K (a i)
abbrev SourceOpen := UnitScaleQuadraticZoomEquiv318.OriginalOpen
  (mapped (K:=K) α) (mapped (K:=K) β) (mapped (K:=K) γ)
abbrev GenericChart := K ⊗[V] IntegralZoomNeighborhood318.Chart V α β γ t

theorem mapped_root_equation (i : Fin 4) : (mapped (K:=K) y i)^2=
    IntegralQuadraticPointZoom318.value (mapped (K:=K) α) (mapped (K:=K) β)
      (mapped (K:=K) γ) (algebraMap V K t) i := by
  have h := congrArg (algebraMap V K) (hy i)
  simpa only [mapped,IntegralQuadraticPointZoom318.value,map_add,map_mul,map_pow] using h

/-- The actual generic fiber of the constructed integral smooth chart is
isomorphic to the actual original noncontact source open. Both inverse
maps are built on whole rings. No point-surjectivity surrogate is used. -/
@[expose] def equivalence : SourceOpen (K:=K) α β γ ≃ₐ[K] GenericChart (K:=K) α β γ t :=
  (FieldQuadraticZoomEquiv318.algebraEquivalence (mapped (K:=K) α) (mapped (K:=K) β)
    (mapped (K:=K) γ) (algebraMap V K t) (mapped (K:=K) y)
    (mapped_root_equation α β γ t y hy) hn).trans
      (IntegralZoomBaseChange318.equivalence (S:=K) α β γ t).symm

theorem root (i : Fin 4) : equivalence (K:=K) α β γ t y hy hn
    (algebraMap _ (SourceOpen (K:=K) α β γ)
      (FourRootOrderSigns318.generator
        (UnitScaleQuadraticZoomEquiv318.originalCoefficient
          (mapped (K:=K) α) (mapped (K:=K) β) (mapped (K:=K) γ)) i))=
    1 ⊗ₜ[V] IntegralZoomNeighborhood318.oldRoot V α β γ t y i := by
  apply (IntegralZoomBaseChange318.equivalence (S:=K) α β γ t).injective
  rw [equivalence,AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply,
    IntegralZoomBaseChange318.equivalence_oldRoot]
  exact FieldQuadraticZoomEquiv318.root _ _ _ _ _ _ _ i

theorem coordinate : equivalence (K:=K) α β γ t y hy hn
    (algebraMap _ (SourceOpen (K:=K) α β γ)
      (algebraMap K[X] (UnitScaleQuadraticZoomEquiv318.originalOrder
        (mapped (K:=K) α) (mapped (K:=K) β) (mapped (K:=K) γ)) Polynomial.X))=
    1 ⊗ₜ[V] IntegralZoomNeighborhood318.oldCoordinate V α β γ t := by
  apply (IntegralZoomBaseChange318.equivalence (S:=K) α β γ t).injective
  rw [equivalence,AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply,
    IntegralZoomBaseChange318.equivalence_oldCoordinate]
  exact FieldQuadraticZoomEquiv318.coordinate _ _ _ _ _ _ _

theorem scalar (k : K) : equivalence (K:=K) α β γ t y hy hn
    (algebraMap K (SourceOpen (K:=K) α β γ) k)=algebraMap K (GenericChart (K:=K) α β γ t) k :=
  (equivalence α β γ t y hy hn).commutes k
end IntegralZoomGenericOpen318
