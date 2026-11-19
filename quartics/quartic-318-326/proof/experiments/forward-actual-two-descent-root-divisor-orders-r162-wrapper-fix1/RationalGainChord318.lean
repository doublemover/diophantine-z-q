module
public import Mathlib.Tactic
public section
namespace RationalGainChord318

/-- Distinct gains on the one prescribed rational conic, including the points with Y=0. -/
def Gains (β θ : ℚ) : Prop :=
  ∃ e f y z w : ℚ, e ≠ f ∧ w ≠ 0 ∧
    y^2 = β*(1-e)*(1+3*e) ∧ z^2 = β*(1-f)*(1+3*f) ∧ e*f = θ*w^2

/-- A single simultaneous rational search, not a local-to-global principle. -/
def Search (β θ : ℚ) : Prop :=
  ∃ c k u s : ℚ, u ≠ 0 ∧ s ≠ 0 ∧
    θ*u^2 = (β*c^2-1)*(12+β*k^2) ∧ s^2 = 16+β*(k-2*c)*(k+6*c)

private def D (β k : ℚ) := 12+β*k^2
private def C (β c k : ℚ) := 4+2*β*c*k
private def K (β c : ℚ) := 4*(β*c^2-1)
private def P (β c k e : ℚ) := D β k*e^2-2*C β c k*e+K β c

private theorem positiveD {β : ℚ} (hβ : 0 < β) (k : ℚ) : 0 < D β k := by
  unfold D
  positivity

private theorem identity (β c k e : ℚ) :
    β*P β c k e = 4*((β*c-β*k*e/2)^2-β*(1-e)*(1+3*e)) := by
  unfold P D C K
  ring

theorem gains_to_search {β θ : ℚ} (hβ : 0 < β) (hg : Gains β θ) : Search β θ := by
  obtain ⟨e,f,y,z,w,hef,hw,hy,hz,hefθ⟩ := hg
  let m := (y-z)/(e-f)
  let c := (y-m*e)/β
  let k := -2*m/β
  have hm : m*(e-f)=y-z := by dsimp [m]; field_simp [sub_ne_zero.mpr hef] <;> ring
  have hbc : β*c=y-m*e := by dsimp [c]; field_simp [hβ.ne'] <;> ring
  have hbk : β*k= -2*m := by dsimp [k]; field_simp [hβ.ne'] <;> ring
  have hye : β*c-β*k*e/2=y := by rw [hbc,hbk]; ring
  have hzf : β*c-β*k*f/2=z := by rw [hbc,hbk]; linear_combination -hm
  have he : P β c k e=0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hβ.ne'
    rw [identity,hye,hy] <;> ring
  have hf : P β c k f=0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hβ.ne'
    rw [identity,hzf,hz] <;> ring
  have hsum : D β k*(e+f)-2*C β c k=0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hef)
    unfold P at he hf
    linear_combination he - hf
  have hadd : D β k*(e+f)=2*C β c k := sub_eq_zero.mp hsum
  have hp : D β k*(e*f)=K β c := by
    unfold P at he
    linear_combination e*hsum - he
  have hd := (positiveD hβ k).ne'
  refine ⟨c,k,D β k*w/2,D β k*(e-f)/4,?_,?_,?_,?_⟩
  · exact div_ne_zero (mul_ne_zero hd hw) (by norm_num)
  · exact div_ne_zero (mul_ne_zero hd (sub_ne_zero.mpr hef)) (by norm_num)
  · calc
      θ*(D β k*w/2)^2 = D β k*(D β k*(θ*w^2))/4 := by ring
      _ = _ := by rw [←hefθ,hp]; unfold K D; ring
  · calc
      (D β k*(e-f)/4)^2 = ((D β k*(e+f))^2 - 4*D β k*(D β k*(e*f)))/16 := by ring
      _ = _ := by rw [hadd,hp]; unfold K D C; ring

theorem search_to_gains {β θ : ℚ} (hβ : 0 < β) (hg : Search β θ) : Gains β θ := by
  obtain ⟨c,k,u,s,hu,hs,hmark,hsec⟩ := hg
  let e := (C β c k + 2*s)/(D β k)
  let f := (C β c k - 2*s)/(D β k)
  have hd := (positiveD hβ k).ne'
  have he : D β k*e=C β c k+2*s := by dsimp [e]; field_simp [hd] <;> ring
  have hf : D β k*f=C β c k-2*s := by dsimp [f]; field_simp [hd] <;> ring
  have hdisc : C β c k^2-D β k*K β c=4*s^2 := by
    rw [hsec]; unfold C D K; ring
  have hquad (x : ℚ) (hx : (D β k*x-C β c k)^2=4*s^2) : P β c k x=0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hd
    unfold P
    linear_combination hx - hdisc
  have hpe := hquad e (by rw [he]; ring)
  have hpf := hquad f (by rw [hf]; ring)
  have hnum : (C β c k+2*s)*(C β c k-2*s)=θ*(2*u)^2 := by
    unfold C
    linear_combination -4*hsec - 4*hmark
  refine ⟨e,f,β*c-β*k*e/2,β*c-β*k*f/2,2*u/(D β k),?_,?_,?_,?_,?_⟩
  · intro hh
    rw [hh,hf] at he
    exact hs (by linarith)
  · exact div_ne_zero (mul_ne_zero (by norm_num) hu) hd
  · have hi := identity β c k e
    rw [hpe] at hi
    linarith
  · have hi := identity β c k f
    rw [hpf] at hi
    linarith
  · dsimp [e,f]
    field_simp [hd] <;> nlinarith [hnum]

theorem exact_chord_iff {β θ : ℚ} (hβ : 0 < β) : Gains β θ ↔ Search β θ :=
  ⟨gains_to_search hβ,search_to_gains hβ⟩

end RationalGainChord318
