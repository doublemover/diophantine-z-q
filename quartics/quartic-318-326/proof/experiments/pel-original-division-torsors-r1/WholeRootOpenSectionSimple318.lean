module
public import LocallyInjectiveRootProjectionSimple318
public import WholePolynomialSimpleFiberDensity318
public section
noncomputable section
namespace WholeRootOpenSectionSimple318
open Set Polynomial MonicRootProjectionOpen318
variable {ι : Type} [Fintype ι]

/-- A continuous root section is needed only on an actual open base
neighborhood. Local injectivity still refers to the WHOLE root model,
and generic separability is restricted from the whole base by openness. -/
theorem derivative_ne_zero (Q : Polynomial (MvPolynomial ι ℂ)) (hm : Q.Monic)
    (hs : (Q.map (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)))).Separable)
    (W : Set (ι → ℂ)) (hW : IsOpen W) (b : W → ℂ) (hb : Continuous b)
    (hroot : ∀ y : W, (Q.map (MvPolynomial.eval y.val)).IsRoot (b y))
    (x : W)
    (V : Set (Roots (fun v : ι → ℂ => Q.map (MvPolynomial.eval v))))
    (hV : IsOpen V)
    (hx : (⟨(x.val,b x),hroot x⟩ : Roots (fun v : ι → ℂ =>
      Q.map (MvPolynomial.eval v))) ∈ V)
    (hinj : Set.InjOn (fun q : Roots (fun v : ι → ℂ =>
      Q.map (MvPolynomial.eval v)) => q.val.1) V) :
    (Q.map (MvPolynomial.eval x.val)).derivative.eval (b x) ≠ 0 := by
  let p : W → Polynomial ℂ := fun y => Q.map (MvPolynomial.eval y.val)
  let forget : Roots p → Roots (fun v : ι → ℂ => Q.map (MvPolynomial.eval v)) :=
    fun q => ⟨(q.val.1.val,q.val.2),q.property⟩
  have hforget : Continuous forget :=
    (((continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  have hcoeff (k : ℕ) : Continuous (fun y : W => (p y).coeff k) := by
    have h : Continuous (fun v : ι → ℂ => MvPolynomial.eval v (Q.coeff k)) :=
      continuous_iff_continuousAt.mpr (fun v =>
        ((AnalyticOnNhd.eval_mvPolynomial _) v (mem_univ v)).continuousAt)
    simpa only [p,Polynomial.coeff_map] using h.comp continuous_subtype_val
  have hdense : Dense {y : W | (p y).Separable} :=
    (WholePolynomialSimpleFiberDensity318.dense_separable Q hm hs).preimage
      hW.isOpenMap_subtype_val
  apply LocallyInjectiveRootProjectionSimple318.derivative_ne_zero p Q.natDegree
    (fun y => hm.map _) (fun y => hm.natDegree_map _) hcoeff b hb hroot hdense x
    (forget ⁻¹' V) (hV.preimage hforget) hx
  intro q hq r hr he
  have hfull : forget q = forget r := hinj hq hr (congrArg Subtype.val he)
  apply Subtype.ext
  apply Prod.ext he
  exact congrArg (fun z => z.val.2) hfull
end WholeRootOpenSectionSimple318
