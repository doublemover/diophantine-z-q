module
public import OriginalAffineLeadingForms318
public section
noncomputable section
namespace OriginalFiveGridLeading318
open MvPolynomial TernaryQuadraticLineCover318 OriginalReducedResidueBounds318
open OriginalAffineLeadingForms318
set_option maxHeartbeats 5000000

/-- Exact finite5x5 avoidance, using the pinned Schwartz-Zippel theorem
on the actual polynomial. Degree4 cannot vanish on all25 grid points. -/
lemma five_grid {F : Type*} [Field F] [DecidableEq F]
    (f : MvPolynomial (Fin 2) F) (hf : f≠0) (hd : f.totalDegree≤4)
    (S : Finset F) (hS : S.card=5) :
    ∃ x : Fin 2 → F, x∈Fintype.piFinset (fun _ => S) ∧ eval x f≠0 := by
  classical
  by_contra hh
  push_neg at hh
  have he : (Fintype.piFinset (fun _ : Fin 2 => S)).filter (fun x => eval x f=0)=
      Fintype.piFinset (fun _ : Fin 2 => S) := Finset.filter_eq_self.mpr hh
  have hs := schwartz_zippel_totalDegree hf S
  rw [he] at hs
  have hc : (Fintype.piFinset (fun _ : Fin 2 => S)).card=25 := by
    simp [Fintype.piFinset,hS]
  have hs' : (1:ℚ≥0)≤(f.totalDegree:ℚ≥0)/5 := by simpa [hc,hS] using hs
  have hd' : (f.totalDegree:ℚ≥0)≤4 := by exact_mod_cast hd
  have htop : (f.totalDegree:ℚ≥0)/5≤4/5 :=
    div_le_div_of_nonneg_right hd' (by norm_num)
  have hbad := hs'.trans htop
  norm_num at hbad

@[expose] def grid (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Finset.range 5).image (fun i => (i:ZMod p))

lemma grid_card (p : ℕ) [Fact p.Prime] (hp : 5≤p) : (grid p).card=5 := by
  have hi : Set.InjOn (fun i : ℕ => (i:ZMod p)) (Finset.range 5 : Set ℕ) := by
    intro i hi j hj he
    have hip : i<p := (Finset.mem_range.mp hi).trans_le hp
    have hjp : j<p := (Finset.mem_range.mp hj).trans_le hp
    have hh := congrArg ZMod.val he
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hip,Nat.mod_eq_of_lt hjp] using hh
  rw [grid,Finset.card_image_of_injOn hi,Finset.card_range]

lemma simultaneous_eval {F : Type*} [Field F] (κ t : F) (u v z : Vector F) (i j : F) :
    eval ![i,j] (simultaneousLeading κ t u v z)=
      κ*(fieldSynthesis u v z (i,j,1)).2.2^2*
        quadratic κ t (fieldSynthesis u v z (i,j,1)) := by
  simp [simultaneousLeading,leadingFirst,leadingSecond,row,quadratic,fieldSynthesis]
  ring

/-- A bounded shear is PRODUCED for every prime at least5. Both original
leading coefficients are simultaneously nonzero, including t=-2 modulo p.
No additional content/leading-prime exclusion is assumed. -/
theorem actual_field_shear (p : ℕ) [Fact p.Prime] (hp : 5≤p)
    (κ t : ZMod p) (hκ : κ≠0) (u v z : Vector (ZMod p))
    (hs : Function.Surjective (fieldSynthesis u v z)) :
    ∃ i j : ℕ, i<5 ∧ j<5 ∧
      κ*(fieldSynthesis u v z ((i:ZMod p),(j:ZMod p),1)).2.2^2≠0 ∧
      quadratic κ t (fieldSynthesis u v z ((i:ZMod p),(j:ZMod p),1))≠0 := by
  have h2 : (2:ZMod p)≠0 := by
    intro he
    have hh := congrArg ZMod.val he
    have hp2 : 2<p := by omega
    norm_num [ZMod.val_natCast,Nat.mod_eq_of_lt hp2] at hh
  obtain ⟨x,hx,he⟩ := five_grid (simultaneousLeading κ t u v z)
    (simultaneous_nonzero κ t hκ u v z h2 hs) (simultaneous_degree κ t u v z)
    (grid p) (grid_card p hp)
  have h0 := Fintype.mem_piFinset.mp hx 0
  have h1 := Fintype.mem_piFinset.mp hx 1
  obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp h0
  obtain ⟨j,hj,hej⟩ := Finset.mem_image.mp h1
  have hex : x=![(i:ZMod p),(j:ZMod p)] := by
    funext k
    fin_cases k
    · exact hei.symm
    · exact hej.symm
  rw [hex,simultaneous_eval] at he
  exact ⟨i,j,Finset.mem_range.mp hi,Finset.mem_range.mp hj,
    (mul_ne_zero_iff.mp he).1,(mul_ne_zero_iff.mp he).2⟩

end OriginalFiveGridLeading318
