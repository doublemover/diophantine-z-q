module
public import AnalyticSquareRemovable318
public import PuncturedSquareCoordinate318
public import Mathlib.Tactic.FinCases
public section
noncomputable section
namespace FourRootFiniteBranchExtension318
open Set Filter
open scoped Topology
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (j:Fin 4)

/-- ALL four coordinates of the SAME punctured original map extend at
an actual finite branch. The ramified root has an invertible derivative;
the other three have nonzero centers. No sheet matching or continuity at
the missing point is assumed. -/
theorem extend (z:Fin 4→ℂ→ℂ)
    (hd:∀k,∀ᶠw in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ (z k) w)
    (he:∀k,∀ᶠw in 𝓝[≠] (0:ℂ),(z k w)^2=b j-b k+w^2) :
    ∃Z:Fin 4→ℂ→ℂ,∃inv:ℂ→ℂ,
      (∀k,AnalyticAt ℂ (Z k) 0) ∧
      (∀k,Z k=ᶠ[𝓝[≠] (0:ℂ)] z k) ∧
      (∀k,(Z k 0)^2=b j-b k) ∧ Z j 0=0 ∧
      (∀k,k≠j→Z k 0≠0) ∧ deriv (Z j) 0^2=1 ∧
      AnalyticAt ℂ inv 0 ∧ inv 0=0 ∧
      (fun w=>inv (Z j w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>Z j (inv w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠw in 𝓝 (0:ℂ),∀k,(Z k w)^2=b j-b k+w^2) := by
  have allExt:∀k,∃F:ℂ→ℂ,AnalyticAt ℂ F 0 ∧
      F=ᶠ[𝓝[≠] (0:ℂ)] z k ∧ F 0^2=b j-b k ∧
      (∀ᶠw in 𝓝 (0:ℂ),F w^2=b j-b k+w^2):=by
    intro k
    obtain ⟨F,hF,hFz,h0,hall⟩:=AnalyticSquareRemovable318.extend (z k)
      (fun w=>b j-b k+w^2) (analyticAt_const.add (analyticAt_id.pow 2)) (hd k) (he k)
    refine ⟨F,hF,hFz,?_,hall⟩
    simpa only [zero_pow (by decide:2≠0),add_zero] using h0
  choose Z hZ hZz hZ0 hZsq using allExt
  have hj:∀ᶠw in 𝓝[≠] (0:ℂ),(z j w)^2=w^2:=by
    simpa only [sub_self,zero_add] using he j
  obtain ⟨q,inv,hq,hq0,hqz,hqd,hinv,hinv0,hleft,hright,hqsq⟩:=
    PuncturedSquareCoordinate318.extend (z j) (hd j) hj
  have hZj0:Z j 0=0:=by
    have h:=hZ0 j
    rw [sub_self] at h
    exact pow_eq_zero h
  have hsame:Z j=ᶠ[𝓝 (0:ℂ)] q:=by
    have hp:Z j=ᶠ[𝓝[≠] (0:ℂ)] q:=(hZz j).trans hqz.symm
    filter_upwards [eventually_nhdsWithin_iff.mp hp] with w hw
    by_cases hw0:w=0
    · rw [hw0,hZj0,hq0]
    · exact hw hw0
  have hne:∀k,k≠j→Z k 0≠0:=by
    intro k hk hz
    have h:=hZ0 k
    rw [hz,zero_pow (by decide:2≠0)] at h
    exact hk (hb (sub_eq_zero.mp h.symm)).symm
  have hder:deriv (Z j) 0^2=1:=by rw [hsame.deriv_eq];exact hqd
  have hli:(fun w=>inv (Z j w))=ᶠ[𝓝 (0:ℂ)] id:=by
    filter_upwards [hsame,hleft] with w hw hl
    rw [hw]
    exact hl
  have hri:(fun w=>Z j (inv w))=ᶠ[𝓝 (0:ℂ)] id:=by
    have hi:∀ᶠw in 𝓝 (0:ℂ),Z j (inv w)=q (inv w):=
      hinv.continuousAt.eventually (by simpa only [hinv0] using hsame)
    exact hi.trans hright
  have hall:∀ᶠw in 𝓝 (0:ℂ),∀k,(Z k w)^2=b j-b k+w^2:=by
    filter_upwards [hZsq 0,hZsq 1,hZsq 2,hZsq 3] with w h0 h1 h2 h3
    intro k
    fin_cases k <;> assumption
  exact ⟨Z,inv,hZ,hZz,hZ0,hZj0,hne,hder,hinv,hinv0,hli,hri,hall⟩
end FourRootFiniteBranchExtension318
