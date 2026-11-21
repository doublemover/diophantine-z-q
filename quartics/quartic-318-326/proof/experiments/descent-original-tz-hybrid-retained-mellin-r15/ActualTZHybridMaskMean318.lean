module
public import ActualTZHybridMeanRate318
public import ActualTZHybridOrderedMeaning318
import all ActualTZHybridGrid318
public import ActualTZFiniteCutoffUniformity318
import all ActualTZHybridMeanAverage318
import all ActualTZHybridMeanCell318
import all ActualTZExactZeroIntegerGrid318
public section
noncomputable section
namespace ActualTZHybridMaskMean318
open scoped BigOperators Topology
open Filter MeasureTheory
open ActualTZHybridCanonicalWrap318 ActualTZHybridMeanAverage318 ActualTZHybridMeanCell318
open ActualTZHybridMeanRate318
open ActualTZHybridGlobalLocalStencil318 (Bits)
open ActualTZHybridGrid318 (Ordered lengths_min orderedEquiv pack)
open ActualTZHybridOrderedMeaning318 (exactShift packed_off mixed)
open ActualTZExactZeroIntegerGrid318 ActualPointedCyclicPairing318 ActualTZOldProductAverage318
open ActualTZCanonicalWrapFibres318 ActualTZOneAxisLocalDual318 (prob_swap)
open ActualTZLiteralSchwartz318 ActualTZLiteralOrdinaryBound318 ActualTZOneDivisorExpansion318

variable {I : Type*} [Fintype I] [DecidableEq I] {a t s : ℕ}

abbrev Selected (m : I→Bool) := {i : I // m i=true}

@[expose] def subset (X : Context a t s I) (m : I→Bool) : Context a t s (Selected m) where
  y := X.y
  N := X.N
  n := X.n
  J := X.J
  q := X.q
  b := X.b
  hn := X.hn
  hJ := X.hJ
  hq := X.hq
  D := X.D
  C := X.C
  hM := X.hM
  M := X.M
  global_small := X.global_small
  local_small := X.local_small
  sample := X.sample
  cut := X.cut
  unit := X.unit
  divided := X.divided
  divided_bound := X.divided_bound
  divided_ne := X.divided_ne
  site i := X.site i.val
  distinct i j h := Subtype.ext (X.distinct h)

@[expose] def ν (X : Context a t s I) (α R : ℝ) (χ : ℝ→ℝ) (x : Fin X.n) : ℝ :=
  weightedSquare α R χ (((primorial X.y):ℤ)*((x.val:ℤ)+1)+X.b).natAbs

@[expose] def raw (X : Context a t s I) (m : I→Bool) (α R : ℝ) (χ : ℝ→ℝ) : ℝ :=
  prob (fun x : Fin X.n=>prob (fun z : Ordered a t s X.J X.M=>∏ i : I,if m i then
    ν X α R χ (move X.hn (exactShift X.q X.actualSlope (X.site i) z) x) else 1))

private theorem normalized (X : Context a t s I) (z : X.G) : X.mass z=
    1/(Fintype.card X.G:ℝ) := by
  have H : (∑ _ : X.G,(uniform X.lens:ℝ))=1 := by
    exact_mod_cast uniform_one X.lens (fun i=>(lt_min X.hJ X.hM).trans_le (lengths_min i))
  have hn : (0:ℝ)<Fintype.card X.G := by
    letI : Nonempty X.G := ⟨z⟩
    exact_mod_cast Fintype.card_pos
  change (uniform X.lens:ℝ)=_
  apply (eq_div_iff hn.ne').2
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using H

private theorem exact_site (X : Context a t s I) (z : Ordered a t s X.J X.M) (x : Fin X.n) (i : I)
    (α R : ℝ) (χ : ℝ→ℝ) :
    weightedSquare α R χ
      (oldSite X (pack z) ((x.val:ℤ)+1) i).natAbs=
    ν X α R χ (move X.hn (exactShift X.q X.actualSlope (X.site i) z) x) := by
  have h : X.offset (pack z) i=exactShift X.q X.actualSlope (X.site i) z :=
    packed_off _ _ _ _
  have hRep : residue X.n ((x.val:ℤ)+1+exactShift X.q X.actualSlope (X.site i) z)=
      ((move X.hn (exactShift X.q X.actualSlope (X.site i) z) x).val:ℤ)+1 := by
    rw [move_val]
    unfold residue
    rw [show (x.val:ℤ)+1+exactShift X.q X.actualSlope (X.site i) z-1=(x.val:ℤ)+exactShift X.q X.actualSlope (X.site i) z by ring]
    ring
  rw [oldSite,h,hRep,ν]

/-- Full cyclic mean on the exact ordered pair boxes equals the
physical cyclic mean in the Mellin/CRT splice. Its masks are
selected, never combined by coincident residues. -/
theorem raw_exact (X : Context a t s I) (m : I→Bool) (α R : ℝ) (χ : ℝ→ℝ) :
    raw X m α R χ=original (subset X m) α R χ := by
  classical
  let U := subset X m
  let F (z : X.G) (x : Fin X.n) :=
    ∏ i : Selected m,weightedSquare α R χ
      (oldSite X z ((x.val:ℤ)+1) i.val).natAbs
  have hre (z : Ordered a t s X.J X.M) (x : Fin X.n) :
      (∏ i : I,if m i then ν X α R χ (move X.hn (exactShift X.q X.actualSlope (X.site i) z) x) else 1)=
        F (pack z) x := by
    unfold F
    rw [←Finset.prod_filter]
    let g (i : I) := ν X α R χ (move X.hn (exactShift X.q X.actualSlope (X.site i) z) x)
    have H : (∏ i∈Finset.univ.filter (fun i=>m i=true),g i)=
        ∏ i : Selected m,g i.val :=
      Finset.prod_subtype (Finset.univ.filter (fun i=>m i=true))
        (fun i=>by simp only [Finset.mem_filter,Finset.mem_univ,true_and]) g
    change (∏ i∈Finset.univ.filter (fun i=>m i=true),g i)=_
    rw [H]
    exact Finset.prod_congr rfl (fun i _=>(exact_site X z x i.val α R χ).symm)
  unfold raw
  simp only [hre]
  have hperm (x : Fin X.n) :
      prob (fun z : Ordered a t s X.J X.M=>F (pack z) x)=prob (fun z : X.G=>F z x) :=
    permute (orderedEquiv a t s X.J X.M) _
  simp only [hperm]
  rw [prob_swap]
  change prob (fun z : X.G=>prob (F z))=original U α R χ
  have hmass (z : X.G) : U.mass z=1/(Fintype.card X.G:ℝ) := normalized X z
  unfold original prob
  change (∑ z : X.G,(∑ x : Fin X.n,F z x)/(Fintype.card (Fin X.n):ℝ))/(Fintype.card X.G:ℝ)=
    ∑ z : X.G,U.mass z*((∑ x : Fin X.n,F z x)/(X.n:ℝ))
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  rw [hmass z,Fintype.card_fin]
  ring

/-- Exact client for the full literal mixed site type. It does not
rename h or x between the selected mask and the signed assignment. -/
theorem raw_eq_mixed (X : Context a t s (Bits a t)) (hs : X.site=id)
    (m : Bits a t→Bool) (α R : ℝ) (χ : ℝ→ℝ) :
    raw X m α R χ=mixed (J:=X.J) (M:=X.M) X.hn X.q X.actualSlope
      (fun w x=>if m w then ν X α R χ x else 1) := by
  simp only [raw,mixed,hs,id_eq]

/-- One finite-exhaustion threshold before masks, common residue,
literal frequency and heterogeneous hybrid chart. Finite rank is the number of
tracked sites, not the number of new coordinates or wrap keys. -/
theorem all_masks (C : Cutoff) (hχ : (∫ t in (0:ℝ)..1,|deriv C.χ t|^2)=1)
    (B σ : ℝ) (hB : ∀ t,|C.χ t|≤B) (hσ : 0<σ) (D c : ℕ)
    (hsmall : 8*(Fintype.card I:ℝ)*σ<1) (l : ℕ→ℝ) (hl : ∀ y,0<l y) :
    ∃ E : ℕ→ℝ,Tendsto E atTop (𝓝 0)∧(∀ y,0≤E y)∧
      ∃ y₀ : ℕ,∀ y≥y₀,∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,∀ (X : Context a t s I),
        scales X y N (l y)→X.cap=c→X.q≤(primorial y)^D→
        ∀ m : I→Bool,|raw X m (α (primorial y)) ((X.n:ℝ)^σ) C.χ-1|≤E y+ε := by
  classical
  let P (m : I→Bool) (y N : ℕ) (ε : ℝ) :=
    ∀ X : Context a t s I,scales X y N (l y)→X.cap=c→X.q≤(primorial y)^D→
      |raw X m (α (primorial y)) ((X.n:ℝ)^σ) C.χ-1|≤ε
  have h (m : I→Bool) : ∃ e : ℕ→ℝ,Tendsto e atTop (𝓝 0)∧(∀ y,0≤e y)∧
      ∃ y₀ : ℕ,∀ y≥y₀,∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,P m y N (e y+ε) := by
    have hCard : (Fintype.card (Selected m):ℝ)≤Fintype.card I := by
      exact_mod_cast Fintype.card_subtype_le (fun i=>m i=true)
    have hRank : 8*(Fintype.card (Selected m):ℝ)*σ<1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCard (by norm_num)) hσ.le) hsmall
    obtain ⟨e,hE,hEn,y₀,hRate⟩ := mask_rate (I:=Selected m) (a:=a) (t:=t) (s:=s) C hχ B σ hB hσ D c hRank
    refine ⟨e,hE,hEn,y₀,?_⟩
    intro y hy ε hε
    obtain ⟨N₀,hN₀⟩ := hRate y hy ε hε (l y) (hl y)
    refine ⟨N₀,?_⟩
    intro N hN X hS hc hQ
    rw [raw_exact]
    exact hN₀ N hN (subset X m) hS hc hQ
  let e (m : I→Bool) := Classical.choose (h m)
  have hE (m : I→Bool) := Classical.choose_spec (h m)
  have hm (m : I→Bool) (y N : ℕ) {a b : ℝ} (hab : a≤b) (H : P m y N a) :
      P m y N b := fun X hS hc hQ=>(H X hS hc hQ).trans hab
  obtain ⟨E,hT,hE0,y₀,hY⟩ :=
    ActualTZFiniteCutoffUniformity318.finite_rate P e (fun m=>(hE m).1)
      (fun m=>(hE m).2.1) hm (fun m=>(hE m).2.2)
  refine ⟨E,hT,hE0,y₀,?_⟩
  intro y hy ε hε
  obtain ⟨N₀,hN₀⟩ := hY y hy ε hε
  exact ⟨N₀,fun N hN X hS hc hQ m=>hN₀ N hN m X hS hc hQ⟩

end ActualTZHybridMaskMean318
