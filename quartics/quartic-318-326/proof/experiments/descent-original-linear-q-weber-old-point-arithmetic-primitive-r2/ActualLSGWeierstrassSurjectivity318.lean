module
public import ActualVendorLSGWeierstrassDictionary318
public section
noncomputable section

namespace ActualLSGWeierstrassSurjectivity318

open Complex Filter Set WeierstrassCurve WeierstrassCurve.Affine
open LSG.Weierstrass
open scoped Topology

private theorem lattice_discr (L : PeriodPair) : Discr (L.lattice : Set ℂ) := by
  change Discr {u : ℂ | u ∈ L.lattice}
  simpa only [add_zero] using discr_add L 0

/-- At a lattice pole the reciprocal of an omitted wp value is
bounded: its literal expression off the lattice is z²/(1+z²g(z)). -/
private theorem reciprocal_wp_locBdd (L : PeriodPair) (c : ℂ)
    (h : ∀ z ∉ L.lattice, L.weierstrassP z ≠ c) :
    LocBdd (fun z => (L.weierstrassP z-c)⁻¹) 0 := by
  let g : ℂ → ℂ := fun t => (L.weierstrassPExcept 0) t-c
  let D : ℂ → ℂ := fun t => 1+t^2*g t
  let f : ℂ → ℂ := fun t => t^2/D t
  have hZ : ContinuousAt (fun t : ℂ => t^2) 0 := (continuous_id.pow 2).continuousAt
  have hg : ContinuousAt g 0 :=
    (continuousAt_weierstrassPExcept_zero L).sub continuousAt_const
  have hD : ContinuousAt D 0 := continuousAt_const.add (hZ.mul hg)
  have hD₀ : D 0 ≠ 0 := by simp [D]
  obtain ⟨A,hA⟩ := LocBdd.of_continuousAt (hZ.div hD hD₀)
  refine ⟨A,?_⟩
  filter_upwards [hA,lattice_discr L 0] with t ht hLt
  have h₀ : t ≠ 0 := fun ht0 => hLt (ht0.symm ▸ L.lattice.zero_mem)
  have hp : L.weierstrassP t-c ≠ 0 := sub_ne_zero.mpr (h t hLt)
  have hDD : D t=(L.weierstrassP t-c)*t^2 := by
    change 1+t^2*(L.weierstrassPExcept 0 t-c)=_
    rw [weierstrassP_eq_except_zero]
    field_simp [h₀] <;> ring
  have hE : (L.weierstrassP t-c)⁻¹=f t := by
    change (L.weierstrassP t-c)⁻¹=t^2/D t
    rw [hDD]
    field_simp [h₀,hp] <;> ring
  rw [hE]
  exact ht

/-- The pinned LSG dictionary gives degree two but does not state
surjectivity. Obtain it without adding an analytic assumption:
reciprocal of an omitted value is an elliptic function bounded at
all poles, hence constant by the already proved removable/Liouville
bridge. Two points outside its degree-two collision set contradict
that constancy. -/
theorem wp_surjective_off_lattice (L : PeriodPair) (c : ℂ) :
    ∃ w ∉ L.lattice, L.weierstrassP w=c := by
  by_contra H
  have h : ∀ z ∉ L.lattice, L.weierstrassP z ≠ c := fun z hz e => H ⟨z,hz,e⟩
  let f : ℂ → ℂ := fun z => (L.weierstrassP z-c)⁻¹
  have hPer (ω : ℂ) (hω : ω∈L.lattice) (z : ℂ) : f (z+ω)=f z := by
    simp only [f,weierstrassP_add_mem L z hω]
  have hHol (z : ℂ) (hz : z∉L.lattice) : DifferentiableAt ℂ f z := by
    exact ((differentiableAt_weierstrassP L hz).sub_const c).inv (sub_ne_zero.mpr (h z hz))
  have hBound (s : ℂ) (hs : s∈L.lattice) : LocBdd f s := by
    have h0 : LocBdd f 0 := reciprocal_wp_locBdd L c h
    simpa only [zero_add] using h0.of_periodic (hPer s hs)
  obtain ⟨k,hk⟩ := eq_const_of_locBdd L (lattice_discr L)
    (fun _ hx _ hy => L.lattice.add_mem hx hy)
    (fun u _ ω hω => hPer ω hω u) hHol hBound
  obtain ⟨z,hz⟩ := (lattice_discr L).exists_notMem
  obtain ⟨w,hw⟩ := (discr_degS L z).exists_notMem
  have hwL : w∉L.lattice := fun e => hw (Or.inl e)
  have hSame : f w=f z := (hk w hwL).trans (hk z hz).symm
  have hSame' : L.weierstrassP w-c = L.weierstrassP z-c := by
    exact inv_injective hSame
  have hWP : L.weierstrassP w = L.weierstrassP z := by
    linear_combination hSame'
  have he := (weierstrassP_eq_iff L hz hwL).mp hWP
  exact hw (Or.inr he)

private theorem equation_y_square (L : PeriodPair) {x y : ℂ}
    (h : (curveA L).Equation x y) :
    y^2=x^3-(L.g₂/4)*x-L.g₃/4 := by
  rw [equation_iff] at h
  simp only [curveA,curve,zero_mul,zero_add,add_zero] at h
  linear_combination h

/-- Surjectivity onto the very Mathlib stock affine point group of
the donor (not onto a separately defined analytic or projective group). -/
theorem expE_surjective (L : PeriodPair) : Function.Surjective (expE L) := by
  classical
  intro P
  cases P with
  | zero => exact ⟨0,expE_zero L⟩
  | some x y h =>
    obtain ⟨z,hz,hx⟩ := wp_surjective_off_lattice L x
    have hY : (L.derivWeierstrassP z/2)^2=y^2 := by
      have hF := equation_y_square L (equation_weierstrassP L hz)
      rw [hx] at hF
      exact hF.trans (equation_y_square L h.1).symm
    have hFac : (L.derivWeierstrassP z/2-y)*(L.derivWeierstrassP z/2+y)=0 := by
      linear_combination hY
    rcases (mul_eq_zero.mp hFac) with hp|hm
    · refine ⟨z,?_⟩
      rw [expE_of_notMem L hz]
      exact some_eq_some L hx (sub_eq_zero.mp hp)
    · have hNegz : -z∉L.lattice := fun h => hz (by simpa only [neg_neg] using L.lattice.neg_mem h)
      refine ⟨-z,?_⟩
      rw [expE_of_notMem L hNegz]
      apply some_eq_some L
      · rw [L.weierstrassP_neg,hx]
      · rw [L.derivWeierstrassP_neg]
        linear_combination -hm

/-- Kernel is exactly the original period lattice, including the
infinity branch, not just ⊇ from periodicity. -/
theorem expHom_kernel (L : PeriodPair) : (expHom L).ker=L.lattice.toAddSubgroup := by
  ext x
  change expE L x=0 ↔ x∈L.lattice
  by_cases h : x∈L.lattice
  · exact iff_of_true (expE_of_mem L h) h
  · rw [expE_of_notMem L h]
    exact iff_of_false (by
      intro he
      change Point.some _ _ _=Point.zero at he
      cases he) h

end ActualLSGWeierstrassSurjectivity318
