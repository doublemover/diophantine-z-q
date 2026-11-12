module
public import FourRootNormalizedPointCharts318
public import SquareRootAmbientGraph318
public section
noncomputable section
namespace FourRootFiniteBranchGraph318
open Set Filter
open scoped Topology
open FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (j:Fin 4)
variable (p:FinitePoints b) (hp:p.val.1=b j)

include hp in
lemma root_zero : p.val.2 j=0:=by
  have h:=p.property j
  rw [hp,sub_self] at h
  by_contra hz
  exact (pow_ne_zero 2 hz) h
include hb hp in
lemma other_root_ne (k:Fin 4) (hk:k≠j) : p.val.2 k≠0:=by
  intro h
  have hh:=p.property k
  rw [h,zero_pow (by decide:2≠0),hp] at hh
  exact hk (hb (sub_eq_zero.mp hh.symm)).symm

include hb hp in
/-- Three prescribed unit roots and one literal ramified coordinate.
The actual selected point supplies the three signs; none is replaced by
an arbitrary square-root convention. -/
theorem graphs : ∃g:Fin 4→ℂ→ℂ,
    (∀k,k≠j→AnalyticAt ℂ (g k) (b j)) ∧
    (∀k,k≠j→g k (b j)=p.val.2 k) ∧
    (∀k,k≠j→∀t,g k t^2=t-b k) ∧
    (∀k,k≠j→∀ᶠq in 𝓝 (p.val:ℂ×(Fin 4→ℂ)),
      q.2 k^2=q.1-b k → q.2 k=g k q.1) := by
  have hh:∀k:Fin 4,∃g:ℂ→ℂ,k≠j→
      AnalyticAt ℂ g (b j) ∧ g (b j)=p.val.2 k ∧ (∀t,g t^2=t-b k) ∧
      ∀ᶠq in 𝓝 (p.val:ℂ×(Fin 4→ℂ)),q.2 k^2=q.1-b k→q.2 k=g q.1:=by
    intro k
    by_cases hk:k=j
    · exact ⟨fun _=>0,fun hn=>False.elim (hn hk)⟩
    · have hs:p.val.2 k^2=b j-b k:=by rw [←hp];exact p.property k
      obtain ⟨g,hg,hga,hgs,hgu⟩:=SquareRootAmbientGraph318.exists_graph
        (fun t=>t-b k) (b j) (p.val.2 k) (analyticAt_id.sub analyticAt_const)
        (other_root_ne b hb j p hp k hk) hs
      refine ⟨g,fun _=>⟨hg,hga,hgs,?_⟩⟩
      have hc:ContinuousAt (fun q:ℂ×(Fin 4→ℂ)=>(q.1,q.2 k)) p.val:=
        continuousAt_fst.prodMk ((continuous_apply k).continuousAt.comp continuousAt_snd)
      exact hc.eventually (by simpa only [hp] using hgu)
  choose g hg using hh
  exact ⟨g,fun k hk=>(hg k hk).1,fun k hk=>(hg k hk).2.1,
    fun k hk=>(hg k hk).2.2.1,fun k hk=>(hg k hk).2.2.2⟩

include hb hp in
/-- A literal independent target branch graph t=b_j+w². Its inverse is
exactly the j-th original root, and FULL ambient local right inverse is
proved on every nearby point satisfying the four equations. -/
theorem parametrization : ∃Z:ℂ→FinitePoints b,
    Z 0=p ∧
    (∀w,(Z w).val.1=b j+w^2) ∧ (∀w,(Z w).val.2 j=w) ∧
    (∀k,AnalyticAt ℂ (fun w=>(Z w).val.2 k) 0) ∧
    (∀ᶠq in 𝓝 p.val,(∀k,q.2 k^2=q.1-b k)→(Z (q.2 j)).val=q) := by
  obtain ⟨g,hg,hg0,hgs,hgu⟩:=graphs b hb j p hp
  let z:ℂ→Fin 4→ℂ:=fun w k=>if k=j then w else g k (b j+w^2)
  have hz:∀w k,z w k^2=b j+w^2-b k:=by
    intro w k
    by_cases hk:k=j
    · simp [z,hk]
    · dsimp only [z]
      rw [if_neg hk,hgs k hk]
  let Z:ℂ→FinitePoints b:=fun w=>⟨(b j+w^2,z w),hz w⟩
  have hZ0:Z 0=p:=by
    apply Subtype.ext
    apply Prod.ext
    · change b j+(0:ℂ)^2=p.val.1
      simpa only [zero_pow (by decide:2≠0),add_zero] using hp.symm
    · funext k
      by_cases hk:k=j
      · subst k
        simpa [Z,z] using (root_zero b j p hp).symm
      · simpa [Z,z,hk] using hg0 k hk
  refine ⟨Z,hZ0,fun _=>rfl,?_,?_,?_⟩
  · intro w
    simp [Z,z]
  · intro k
    by_cases hk:k=j
    · have hi : AnalyticAt ℂ (fun w:ℂ=>w) 0 := by
        exact (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) (0 : ℂ)).congr
          (Filter.Eventually.of_forall (fun w => rfl))
      simpa only [Z,z,if_pos hk] using hi
    · have ha:AnalyticAt ℂ (g k) (b j+(0:ℂ)^2):=by simpa using hg k hk
      have hi : AnalyticAt ℂ (fun w:ℂ=>w) 0 := by
        exact (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) (0 : ℂ)).congr
          (Filter.Eventually.of_forall (fun w => rfl))
      have hs : AnalyticAt ℂ (fun w:ℂ=>b j+w^2) 0 :=
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ=>b j) 0).add (hi.pow 2)
      have hc : AnalyticAt ℂ (fun w:ℂ=>g k (b j+w^2)) 0 :=
        ha.comp (g := g k) (f := fun w : ℂ => b j+w^2) hs
      simpa only [Z,z,if_neg hk] using hc
  · have hu:∀k,∀ᶠq in 𝓝 p.val,k≠j→q.2 k^2=q.1-b k→q.2 k=g k q.1:=by
      intro k
      by_cases hk:k=j
      · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h hk))
      · exact (hgu k hk).mono (fun q h _=>h)
    filter_upwards [hu 0,hu 1,hu 2,hu 3] with q h0 h1 h2 h3
    intro he
    have hall:∀k,k≠j→q.2 k^2=q.1-b k→q.2 k=g k q.1:=by
      intro k;fin_cases k <;> assumption
    have ht:b j+q.2 j^2=q.1:=by rw [he j];ring
    apply Prod.ext
    · exact ht
    · funext k
      by_cases hk:k=j
      · simp [Z,z,hk]
      · change (if k=j then q.2 j else g k (b j+q.2 j^2))=q.2 k
        rw [if_neg hk,ht]
        exact (hall k hk (he k)).symm
end FourRootFiniteBranchGraph318
