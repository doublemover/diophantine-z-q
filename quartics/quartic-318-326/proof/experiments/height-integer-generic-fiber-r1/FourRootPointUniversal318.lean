module
public import FourRootSignBaseChange318
public section
noncomputable section
namespace FourRootPointUniversal318
open Polynomial FourRootOrder318 FourRootOrderSigns318 QuadraticPresentation318
set_option maxHeartbeats 500000
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (a : Fin 4 → R) (r : Fin 4 → A) (hr : ∀ i, (r i)^2 = algebraMap R A (a i))

@[expose] def rootMap (i : Fin 4) : RootRing (a i) →ₐ[R] A :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R A) (r i) (by
    change Polynomial.aeval (r i) (X^2 - C (a i)) = 0
    simp only [map_sub, map_pow, aeval_X, aeval_C, hr, sub_self])

@[simp] theorem rootMap_root (i : Fin 4) :
    rootMap a r hr i (AdjoinRoot.root (polynomial (a i))) = r i :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The universal map from the original four quadratic tensor factors,
with the chosen four root values and no unproved point-existence premise. -/
@[expose] def point : Order a →ₐ[R] A :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (rootMap a r hr 0) (rootMap a r hr 1) (fun _ _ => Commute.all _ _))
    (Algebra.TensorProduct.lift (rootMap a r hr 2) (rootMap a r hr 3) (fun _ _ => Commute.all _ _))
    (fun _ _ => Commute.all _ _)

@[simp] theorem point_generator (i : Fin 4) : point a r hr (generator a i) = r i := by
  fin_cases i <;> simp [point, generator]

/-- Any original four-root point factors through a subalgebra containing
its actual four roots. -/
@[expose] def factor (p : Order a →ₐ[R] A) (B : Subalgebra R A)
    (hB : ∀ i, p (generator a i) ∈ B) : Order a →ₐ[R] B :=
  point a (fun i => ⟨p (generator a i), hB i⟩) (by
    intro i
    apply Subtype.ext
    change p (generator a i)^2 = algebraMap R A (a i)
    rw [← map_pow, generator_square, AlgHom.commutes])

theorem factor_comp (p : Order a →ₐ[R] A) (B : Subalgebra R A)
    (hB : ∀ i, p (generator a i) ∈ B) : B.val.comp (factor a p B hB) = p := by
  apply FourRootSignBaseChange318.hom_ext
  intro i
  simp [factor, AlgHom.comp_apply]

include hr in
/-- The generators are the exact roots supplied to the universal construction. -/
theorem point_unique (p : Order a →ₐ[R] A)
    (hp : ∀ i, p (generator a i) = r i) : p = point a r hr := by
  apply FourRootSignBaseChange318.hom_ext
  intro i
  rw [point_generator, hp]

end FourRootPointUniversal318
