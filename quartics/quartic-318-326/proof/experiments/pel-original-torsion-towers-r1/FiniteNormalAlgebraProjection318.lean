module
public import FiniteIntegralProjectionOpen318
public import FiniteNormalBaseRootPointLift318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section
namespace FiniteNormalAlgebraProjection318
open Set Polynomial
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable (A : Type) [CommRing A] [IsDomain A]
  [Algebra (MvPolynomial κ ℂ) A] [Algebra ℂ A]
  [IsScalarTower ℂ (MvPolynomial κ ℂ) A]
  [IsTorsionFree (MvPolynomial κ ℂ) A] [Module.Finite (MvPolynomial κ ℂ) A]

/-- Any actual finite normal-base algebra, represented by ALL of its
complex evaluations in a closed affine coordinate model, has OPEN
Euclidean normalization projection. No reduced/monogenic approximation
or dense-open presentation replaces the whole algebra. -/
theorem projection_open
    (a : ι → A) (S : Set (ι → ℂ)) (hS : IsClosed S)
    (e : S → (A →ₐ[ℂ] ℂ))
    (he : ∀ w : S, ∀ i, e w (a i) = w.val i)
    (hs : Function.Surjective e)
    (π : (ι → ℂ) → (κ → ℂ)) (hπ : Continuous π)
    (hb : ∀ w : S, ∀ r : MvPolynomial κ ℂ,
      e w (algebraMap (MvPolynomial κ ℂ) A r) = MvPolynomial.eval (π w.val) r) :
    IsOpenMap (fun w : S => π w.val) := by
  classical
  let R := MvPolynomial κ ℂ
  have relation (t : A) (w : S) :
      ((minpoly R t).map (MvPolynomial.eval (π w.val))).IsRoot (e w t) := by
    have h := congrArg (e w) (minpoly.aeval R t)
    change e w ((minpoly R t).eval₂ (algebraMap R A) t) = e w 0 at h
    have hbase : (e w).toRingHom.comp (algebraMap R A) = MvPolynomial.eval (π w.val) :=
      RingHom.ext (hb w)
    rw [Polynomial.hom_eval₂,hbase,map_zero] at h
    simpa only [Polynomial.IsRoot,Polynomial.eval_map] using h
  apply FiniteIntegralProjectionOpen318.projection_open_of_weight_lifts S hS π hπ
    (fun i => minpoly R (a i))
    (fun i => minpoly.monic (IsIntegral.of_finite R (a i)))
  · intro w hw i
    simpa only [he] using relation (a i) (⟨w,hw⟩ : S)
  · intro u
    let t : A := ∑ i : Fin (Fintype.card ι),
      a ((Fintype.equivFin ι).symm i) * algebraMap ℂ A (u^i.val)
    have ht (w : S) : e w t = FiniteIntegralProjectionOpen318.weight u w.val := by
      simp only [t,map_sum,map_mul,AlgHom.commutes,he,
        FiniteIntegralProjectionOpen318.weight,FiniteComplexFiberSeparation318.weighted]
    refine ⟨minpoly R t,minpoly.monic (IsIntegral.of_finite R t),?_,?_⟩
    · intro w hw
      simpa only [ht] using relation t (⟨w,hw⟩ : S)
    · intro v z hz
      let v' : R →ₐ[ℂ] ℂ := MvPolynomial.aeval v
      obtain ⟨f,hf,hz'⟩ := FiniteNormalBaseRootPointLift318.exists_evaluation R A t v' z hz
      obtain ⟨w,hw⟩ := hs f
      have hv : π w.val = v := by
        funext k
        have h := hf (MvPolynomial.X k)
        rw [←hw,hb] at h
        simpa only [v',MvPolynomial.aeval_X,MvPolynomial.eval_X] using h
      refine ⟨w.val,w.property,hv,?_⟩
      rw [←ht,hw]
      exact hz'
end FiniteNormalAlgebraProjection318
