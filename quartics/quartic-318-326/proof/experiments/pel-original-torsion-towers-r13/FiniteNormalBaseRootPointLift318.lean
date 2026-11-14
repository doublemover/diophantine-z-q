module
public import FiniteNormalBaseMonogenicSuborder318
public import FiniteComplexAlgebraPointLift318
public section
noncomputable section
namespace FiniteNormalBaseRootPointLift318
open Polynomial Algebra
variable (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing A] [IsDomain A] [Algebra R A] [IsTorsionFree R A] [Module.Finite R A]
  [Algebra ℂ R] [Algebra ℂ A] [IsScalarTower ℂ R A]

/-- Every complex root of the actual minimal polynomial of ANY chosen
original element lifts to an evaluation of the WHOLE finite algebra,
over exactly the specified base evaluation. No localization is used. -/
theorem exists_evaluation (t : A) (v : R →ₐ[ℂ] ℂ) (z : ℂ)
    (hz : ((minpoly R t).map v.toRingHom).eval z = 0) :
    ∃ f : A →ₐ[ℂ] ℂ,
      (∀ r : R, f (algebraMap R A r) = v r) ∧ f t = z := by
  let g : AdjoinRoot (minpoly R t) →ₐ[ℂ] A :=
    (FiniteNormalBaseMonogenicSuborder318.embedding R A t).restrictScalars ℂ
  have hg : Function.Injective g := FiniteNormalBaseMonogenicSuborder318.embedding_injective R A t
  have hgf : g.Finite := FiniteNormalBaseMonogenicSuborder318.embedding_finite R A t
  let e : AdjoinRoot (minpoly R t) →ₐ[ℂ] ℂ :=
    AdjoinRoot.liftAlgHom (minpoly R t) v z (by simpa only [Polynomial.eval_map] using hz)
  obtain ⟨f,hf⟩ := FiniteComplexAlgebraPointLift318.exists_lift g hg hgf e
  refine ⟨f,?_,?_⟩
  · intro r
    have h := congrArg (fun h : AdjoinRoot (minpoly R t) →ₐ[ℂ] ℂ =>
      h (algebraMap R (AdjoinRoot (minpoly R t)) r)) hf
    change f (FiniteNormalBaseMonogenicSuborder318.embedding R A t
      (algebraMap R (AdjoinRoot (minpoly R t)) r)) = e _ at h
    rw [(FiniteNormalBaseMonogenicSuborder318.embedding R A t).commutes] at h
    simpa only [e,AdjoinRoot.algebraMap_eq,AdjoinRoot.liftAlgHom_of] using h
  · have h := congrArg (fun h : AdjoinRoot (minpoly R t) →ₐ[ℂ] ℂ =>
      h (AdjoinRoot.root (minpoly R t))) hf
    change f (FiniteNormalBaseMonogenicSuborder318.embedding R A t
      (AdjoinRoot.root (minpoly R t))) = e _ at h
    rw [FiniteNormalBaseMonogenicSuborder318.embedding_root] at h
    simpa only [e,AdjoinRoot.liftAlgHom_root] using h
end FiniteNormalBaseRootPointLift318
