module
public import FiniteNormalAlgebraProjectionProper318
public import ClosedFiberLocalInjectivity318
public section
noncomputable section
namespace FiniteNormalRootLocalInjection318
open Set Polynomial MonicRootProjectionOpen318
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable (A : Type) [CommRing A] [IsDomain A]
  [Algebra (MvPolynomial κ ℂ) A] [Algebra ℂ A]
  [IsScalarTower ℂ (MvPolynomial κ ℂ) A]
  [IsTorsionFree (MvPolynomial κ ℂ) A] [Module.Finite (MvPolynomial κ ℂ) A]

/-- Properness and the WHOLE minimal-polynomial lifting theorem transfer
local injectivity from all actual algebra points to all primitive roots.
The separating assumption concerns the entire chosen algebra fiber. -/
theorem root_projection_locally_injective
    (a : ι → A) (S : Set (ι → ℂ)) (hS : IsClosed S)
    (e : S → (A →ₐ[ℂ] ℂ))
    (he : ∀ w : S, ∀ i, e w (a i) = w.val i)
    (hs : Function.Surjective e)
    (π : (ι → ℂ) → (κ → ℂ)) (hπ : Continuous π)
    (hb : ∀ w : S, ∀ r : MvPolynomial κ ℂ,
      e w (algebraMap (MvPolynomial κ ℂ) A r) = MvPolynomial.eval (π w.val) r)
    (t : A) (T : (ι → ℂ) → ℂ) (hT : Continuous T)
    (hTe : ∀ w : S, e w t = T w.val)
    (x : S)
    (hsep : Set.InjOn (fun f : A →ₐ[ℂ] ℂ => f t)
      {f | ∀ r : MvPolynomial κ ℂ,
        f (algebraMap (MvPolynomial κ ℂ) A r) = MvPolynomial.eval (π x.val) r})
    (U : Set S) (hU : IsOpen U) (hxU : x ∈ U)
    (hinj : Set.InjOn (fun w : S => π w.val) U) :
    let p := fun v : κ → ℂ => (minpoly (MvPolynomial κ ℂ) t).map (MvPolynomial.eval v)
    ∃ hroot : (p (π x.val)).IsRoot (T x.val),
      ∃ V : Set (Roots p), IsOpen V ∧
        (⟨(π x.val,T x.val),hroot⟩ : Roots p) ∈ V ∧
        Set.InjOn (fun q : Roots p => q.val.1) V := by
  let R := MvPolynomial κ ℂ
  let p := fun v : κ → ℂ => (minpoly R t).map (MvPolynomial.eval v)
  have relation (w : S) : (p (π w.val)).IsRoot (T w.val) := by
    have h := congrArg (e w) (minpoly.aeval R t)
    change e w ((minpoly R t).eval₂ (algebraMap R A) t) = e w 0 at h
    have hbase : (e w).toRingHom.comp (algebraMap R A) = MvPolynomial.eval (π w.val) :=
      RingHom.ext (hb w)
    rw [Polynomial.hom_eval₂,hbase,map_zero,hTe] at h
    simpa only [p,Polynomial.IsRoot,Polynomial.eval_map] using h
  let Y := Roots p
  let f : S → Y := fun w => ⟨(π w.val,T w.val),relation w⟩
  let q : Y → (κ → ℂ) := fun y => y.val.1
  have hf : Continuous f :=
    ((hπ.comp continuous_subtype_val).prodMk (hT.comp continuous_subtype_val)).subtype_mk _
  have hq : Continuous q := continuous_fst.comp continuous_subtype_val
  have hp : IsProperMap (q ∘ f) :=
    FiniteNormalAlgebraProjectionProper318.projection_proper A a S hS e he π hπ hb
  have honto : Function.Surjective f := by
    intro y
    let v : R →ₐ[ℂ] ℂ := MvPolynomial.aeval y.val.1
    obtain ⟨l,hl,ht⟩ := FiniteNormalBaseRootPointLift318.exists_evaluation R A t v y.val.2 y.property
    obtain ⟨w,hw⟩ := hs l
    refine ⟨w,Subtype.ext (Prod.ext ?_ ?_)⟩
    · funext k
      have hk := hl (MvPolynomial.X k)
      rw [←hw,hb] at hk
      simpa only [v,MvPolynomial.aeval_X,MvPolynomial.eval_X] using hk
    · change T w.val = y.val.2
      rw [←hTe,hw]
      exact ht
  have hsingle : ∀ w, f w = f x → w = x := by
    intro w hw
    have hv := congrArg (fun y : Y => y.val.1) hw
    have ht := congrArg (fun y : Y => y.val.2) hw
    have hel : e w = e x := hsep
      (fun r => (hb w r).trans (congrArg (fun v => MvPolynomial.eval v r) hv))
      (hb x) (by simpa only [hTe] using ht)
    apply Subtype.ext
    funext i
    rw [←he w i,←he x i,hel]
  exact ⟨relation x,ClosedFiberLocalInjectivity318.transfer f q
    (isProperMap_of_comp_of_t2 hf hq hp).isClosedMap honto x hsingle U hU hxU hinj⟩
end FiniteNormalRootLocalInjection318
