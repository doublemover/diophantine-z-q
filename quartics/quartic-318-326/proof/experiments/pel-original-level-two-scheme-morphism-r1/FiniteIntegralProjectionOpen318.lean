module
public import IntegralCoordinateProperMap318
public import SeparatingClosedProjection318
public import FiniteComplexFiberSeparation318
public import LocalizedMonicRootDensity318
public section
noncomputable section
namespace FiniteIntegralProjectionOpen318
open Set Polynomial
open scoped Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma polynomial_eval_continuous (P : Polynomial (MvPolynomial κ ℂ)) (z : ℂ) :
    Continuous (fun v : κ → ℂ => (P.map (MvPolynomial.eval v)).eval z) := by
  have h : Continuous (fun v : κ → ℂ => MvPolynomial.eval v (P.eval (MvPolynomial.C z))) :=
    continuous_iff_continuousAt.mpr (fun v =>
      ((AnalyticOnNhd.eval_mvPolynomial _) v (mem_univ v)).continuousAt)
  have he (v : κ → ℂ) : (P.map (MvPolynomial.eval v)).eval z =
      MvPolynomial.eval v (P.eval (MvPolynomial.C z)) := by
    simpa only [MvPolynomial.eval_C] using
      (Polynomial.eval_map_apply (p := P) (MvPolynomial.eval v) (MvPolynomial.C z))
  exact h.congr (fun v => (he v).symm)

/-- Literal weighted coordinates after the canonical finite enumeration. -/
@[expose] def weight (t : ℂ) (w : ι → ℂ) : ℂ :=
  FiniteComplexFiberSeparation318.weighted t
    (fun i : Fin (Fintype.card ι) => w ((Fintype.equivFin ι).symm i))

lemma weight_continuous (t : ℂ) : Continuous (weight (ι := ι) t) := by
  classical
  unfold weight FiniteComplexFiberSeparation318.weighted
  exact continuous_finset_sum _ (fun i _ => (continuous_apply _).mul continuous_const)

lemma exists_separating_weight (W : Set (ι → ℂ)) (hW : W.Finite) :
    ∃ t : ℂ, Set.InjOn (weight (ι := ι) t) W := by
  classical
  let r (w : ι → ℂ) : Fin (Fintype.card ι) → ℂ :=
    fun i => w ((Fintype.equivFin ι).symm i)
  have hr : Function.Injective r := by
    intro w w' h
    funext i
    have hi := congrFun h ((Fintype.equivFin ι) i)
    simpa only [r,Equiv.symm_apply_apply] using hi
  obtain ⟨t,ht⟩ := FiniteComplexFiberSeparation318.exists_weighted_injective
    (r '' W) (hW.image r)
  refine ⟨t,?_⟩
  intro w hw w' hw' he
  exact hr (ht ⟨w,hw,rfl⟩ ⟨w',hw',rfl⟩ he)

/-- A proper finite-coordinate projection is open if every actual fiber
has a continuous separating element whose WHOLE monic root model is
surjectively lifted. The separating model can vary with the point; the
base projection itself is fixed throughout. -/
theorem projection_open (S : Set (ι → ℂ)) (hS : IsClosed S)
    (π : (ι → ℂ) → (κ → ℂ)) (hπ : Continuous π)
    (Q : ι → Polynomial (MvPolynomial κ ℂ)) (hm : ∀ i, (Q i).Monic)
    (hroot : ∀ w ∈ S, ∀ i, ((Q i).map (MvPolynomial.eval (π w))).IsRoot (w i))
    (hmodels : ∀ x : S, ∃ t : (ι → ℂ) → ℂ, Continuous t ∧
      Set.InjOn t {w | w ∈ S ∧ π w = π x.val} ∧
      ∃ P : Polynomial (MvPolynomial κ ℂ), P.Monic ∧
        (∀ w ∈ S, (P.map (MvPolynomial.eval (π w))).IsRoot (t w)) ∧
        (∀ v z, (P.map (MvPolynomial.eval v)).IsRoot z →
          ∃ w ∈ S, π w = v ∧ t w = z)) :
    IsOpenMap (fun w : S => π w.val) := by
  have hproper := IntegralCoordinateProperMap318.proper_of_monic_coordinates S hS π hπ Q hm hroot
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro v ⟨x,hx,rfl⟩
  obtain ⟨t,ht,hti,P,hP,hPt,hlift⟩ := hmodels x
  let p (v : κ → ℂ) := P.map (MvPolynomial.eval v)
  let Y := MonicRootProjectionOpen318.Roots p
  let f : S → Y := fun w => ⟨(π w.val,t w.val),hPt w.val w.property⟩
  let g : Y → (κ → ℂ) := fun q => q.val.1
  have hf : Continuous f :=
    ((hπ.comp continuous_subtype_val).prodMk (ht.comp continuous_subtype_val)).subtype_mk _
  have hg : Continuous g := continuous_fst.comp continuous_subtype_val
  have hgf : g ∘ f = fun w : S => π w.val := rfl
  have hs : Function.Surjective f := by
    intro q
    obtain ⟨w,hw,hv,hz⟩ := hlift q.val.1 q.val.2 q.property
    refine ⟨⟨w,hw⟩,Subtype.ext ?_⟩
    exact Prod.ext hv hz
  have ho : IsOpenMap g := MonicRootProjectionOpen318.projection_open p P.natDegree
    (fun v => hP.map _) (fun v => hP.natDegree_map _) (polynomial_eval_continuous P)
  have hxsingle : ∀ x', f x' = f x → x' = x := by
    intro x' he
    have hv := congrArg (fun q : Y => q.val.1) he
    have ht' := congrArg (fun q : Y => q.val.2) he
    exact Subtype.ext (hti ⟨x'.property,hv⟩ ⟨x.property,rfl⟩ ht')
  obtain ⟨V,hV,hxV,hVU⟩ := SeparatingClosedProjection318.neighborhood_image_of_proper f g
    hf hg (hgf.symm ▸ hproper) hs ho x hxsingle U hU hx
  exact Filter.mem_of_superset (hV.mem_nhds hxV) hVU

/-- Every weighted coordinate element has its actual whole monic root
model. Finiteness and a separating weight are now produced internally,
so no point-dependent separation or openness premise remains. -/
theorem projection_open_of_weight_lifts (S : Set (ι → ℂ)) (hS : IsClosed S)
    (π : (ι → ℂ) → (κ → ℂ)) (hπ : Continuous π)
    (Q : ι → Polynomial (MvPolynomial κ ℂ)) (hm : ∀ i, (Q i).Monic)
    (hroot : ∀ w ∈ S, ∀ i, ((Q i).map (MvPolynomial.eval (π w))).IsRoot (w i))
    (hlifts : ∀ t : ℂ, ∃ P : Polynomial (MvPolynomial κ ℂ), P.Monic ∧
      (∀ w ∈ S, (P.map (MvPolynomial.eval (π w))).IsRoot (weight t w)) ∧
      (∀ v z, (P.map (MvPolynomial.eval v)).IsRoot z →
        ∃ w ∈ S, π w = v ∧ weight t w = z)) :
    IsOpenMap (fun w : S => π w.val) := by
  apply projection_open S hS π hπ Q hm hroot
  intro x
  have hf := FiniteComplexFiberSeparation318.finite_fiber S π Q hm hroot (π x.val)
  obtain ⟨t,ht⟩ := exists_separating_weight _ hf
  obtain ⟨P,hP,he,hl⟩ := hlifts t
  exact ⟨weight t,weight_continuous t,ht,P,hP,he,hl⟩

/-- Once actual normalization models supply openness, removing a
nonzero base polynomial is genuinely Euclidean dense in the original
closed coordinate model, including every singular and ramified point. -/
theorem dense_base_nonvanishing (S : Set (ι → ℂ))
    (π : (ι → ℂ) → (κ → ℂ))
    (hopen : IsOpenMap (fun w : S => π w.val))
    (b : MvPolynomial κ ℂ) (hb : b ≠ 0) :
    Dense {w : S | MvPolynomial.eval (π w.val) b ≠ 0} :=
  (LocalizedMonicRootDensity318.polynomial_nonzero_dense b hb).preimage hopen
/-- A genuinely closed ambient image containing an entire nonzero
base-cutoff preimage contains the WHOLE original candidate model. -/
theorem subset_closed_of_base_cutoff (S C : Set (ι → ℂ))
    (π : (ι → ℂ) → (κ → ℂ))
    (hopen : IsOpenMap (fun w : S => π w.val)) (hC : IsClosed C)
    (b : MvPolynomial κ ℂ) (hb : b ≠ 0)
    (hcut : ∀ w ∈ S, MvPolynomial.eval (π w) b ≠ 0 → w ∈ C) : S ⊆ C := by
  have hd := dense_base_nonvanishing S π hopen b hb
  have hc : closure {w : S | MvPolynomial.eval (π w.val) b ≠ 0} ⊆
      (Subtype.val ⁻¹' C : Set S) :=
    closure_minimal (fun w hw => hcut w.val w.property hw)
      (hC.preimage continuous_subtype_val)
  intro w hw
  apply hc (a := (⟨w,hw⟩ : S))
  rw [hd.closure_eq]
  exact mem_univ _
end FiniteIntegralProjectionOpen318
