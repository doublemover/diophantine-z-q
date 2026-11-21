module
public import ActualTZSharedFineMeanAverage318
public import ActualTZSharedFineHybridOrdered318
public import ActualTZOneAxisLocalDual318
import all ActualTZSharedFineHybridGrid318
import all ActualTZSharedFineCanonicalWrap318
import all ActualTZSharedFineMeanAverage318
import all ActualTZSharedFineMeanCell318
import all ActualTZExactZeroIntegerGrid318
public section
noncomputable section
namespace ActualTZSharedFineMaskMean318
open scoped BigOperators Topology
open Filter MeasureTheory
open ActualTZSharedFineCanonicalWrap318 ActualTZSharedFineMeanAverage318 ActualTZSharedFineMeanCell318
open ActualTZSharedFineHybridStencil318 (Bits)
open ActualTZSharedFineHybridGrid318 (Ordered lengths_min orderedEquiv pack)
open ActualTZSharedFineHybridOrdered318 (shift packed_off mixed)
open ActualTZExactZeroIntegerGrid318 ActualPointedCyclicPairing318 ActualTZOldProductAverage318
open ActualTZCanonicalWrapFibres318
open ActualTZOneAxisLocalDual318 (prob_swap)
open ActualTZOneDivisorExpansion318

variable {I : Type*} [Fintype I] [DecidableEq I] {a t b s : ℕ}

abbrev Selected (m : I→Bool) := {i : I // m i=true}

@[expose] def subset (X : Context a t b s I) (m : I→Bool) : Context a t b s (Selected m) where
  y := X.y
  N := X.N
  n := X.n
  J := X.J
  q := X.q
  residueClass := X.residueClass
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

@[expose] def ν (X : Context a t b s I) (α R : ℝ) (χ : ℝ→ℝ) (x : Fin X.n) : ℝ :=
  weightedSquare α R χ (((primorial X.y):ℤ)*((x.val:ℤ)+1)+X.residueClass).natAbs

@[expose] def raw (X : Context a t b s I) (m : I→Bool) (α R : ℝ) (χ : ℝ→ℝ) : ℝ :=
  prob (fun x : Fin X.n=>prob (fun z : Ordered a t b s X.J X.M=>∏ i : I,if m i then
    ν X α R χ (move X.hn (shift X.q X.actualSlope (X.site i) z) x) else 1))

private theorem normalized (X : Context a t b s I) (z : X.G) : X.mass z=
    1/(Fintype.card X.G:ℝ) := by
  have H : (∑ _ : X.G,(uniform X.lens:ℝ))=1 := by
    exact_mod_cast uniform_one X.lens (fun i=>(lt_min X.hJ X.hM).trans_le (lengths_min i))
  have hn : (0:ℝ)<Fintype.card X.G := by
    letI : Nonempty X.G := ⟨z⟩
    exact_mod_cast Fintype.card_pos
  change (uniform X.lens:ℝ)=_
  apply (eq_div_iff hn.ne').2
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using H

private theorem exact_site (X : Context a t b s I) (z : Ordered a t b s X.J X.M) (x : Fin X.n) (i : I)
    (α R : ℝ) (χ : ℝ→ℝ) :
    weightedSquare α R χ
      (oldSite X (pack z) ((x.val:ℤ)+1) i).natAbs=
    ν X α R χ (move X.hn (shift X.q X.actualSlope (X.site i) z) x) := by
  have h : X.offset (pack z) i=shift X.q X.actualSlope (X.site i) z :=
    packed_off _ _ _ _
  have hRep : residue X.n ((x.val:ℤ)+1+shift X.q X.actualSlope (X.site i) z)=
      ((move X.hn (shift X.q X.actualSlope (X.site i) z) x).val:ℤ)+1 := by
    rw [move_val]
    unfold residue
    rw [show (x.val:ℤ)+1+shift X.q X.actualSlope (X.site i) z-1=(x.val:ℤ)+shift X.q X.actualSlope (X.site i) z by ring]
    ring
  rw [oldSite,h,hRep,ν,ActualTZSharedFineCanonicalWrap318.Context.base]

/-- Full cyclic mean on the exact ordered pair boxes equals the
physical cyclic mean in the Mellin/CRT splice. Its masks are
selected, never combined by coincident residues. -/
theorem raw_exact (X : Context a t b s I) (m : I→Bool) (α R : ℝ) (χ : ℝ→ℝ) :
    raw X m α R χ=original (subset X m) α R χ := by
  classical
  let U := subset X m
  let F (z : X.G) (x : Fin X.n) :=
    ∏ i : Selected m,weightedSquare α R χ
      (oldSite X z ((x.val:ℤ)+1) i.val).natAbs
  have hre (z : Ordered a t b s X.J X.M) (x : Fin X.n) :
      (∏ i : I,if m i then ν X α R χ (move X.hn (shift X.q X.actualSlope (X.site i) z) x) else 1)=
        F (pack z) x := by
    unfold F
    rw [←Finset.prod_filter]
    let g (i : I) := ν X α R χ (move X.hn (shift X.q X.actualSlope (X.site i) z) x)
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
      prob (fun z : Ordered a t b s X.J X.M=>F (pack z) x)=prob (fun z : X.G=>F z x) := by
    have HP := permute (orderedEquiv a t b s X.J X.M) (fun z : X.G => F z x)
    change prob (fun z : Ordered a t b s X.J X.M => F (pack z) x) =
      prob (fun z : X.G => F z x) at HP
    exact HP
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
theorem raw_eq_mixed (X : Context a t b s (Bits a t b)) (hs : X.site=id)
    (m : Bits a t b→Bool) (α R : ℝ) (χ : ℝ→ℝ) :
    raw X m α R χ=mixed (J:=X.J) (M:=X.M) X.hn X.q X.actualSlope
      (fun w x=>if m w then ν X α R χ x else 1) := by
  simp only [raw,mixed,hs,id_eq]

end ActualTZSharedFineMaskMean318
