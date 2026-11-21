module
public import ActualTZFirstPETEdgeMarkers318
public import ActualTZOriginalFirstPET318
import all OriginalInteriorTelescoping318
import all ActualTZOriginalFirstPET318
public section
noncomputable section
namespace ActualTZFirstPETEdgeRows318
open OriginalInteriorTelescoping318 ActualTZOriginalFirstPET318 ActualTZFirstPETCopy318
open ActualTZFirstPETEdgeMarkers318
abbrev Nodes (r : Row) := Option (Fin r.k)
abbrev Remaining (r : Row) (p : Nodes r) := {i : Nodes r // i≠p}

@[expose] def dAt (r : Row) : Nodes r→ℤ
  | none=>0
  | some i=>d r i.val

@[expose] def PAt (r : Row) (m : ℤ) : Nodes r→ℤ
  | none=>0
  | some i=>shift r i.val m

@[expose] def bAt (r : Row) : Nodes r→ℤ
  | none=>1
  | some i=>residue r i.val

def kAt (r : Row) : Nodes r→ℤ
  | none=>0
  | some i=>(input r i.val).constTerm

theorem tops_inj (r : Row) (hDist : ∀ i j : Fin r.k,i ≠ j → r.ci i.val ≠ r.ci j.val)
    (hFresh : ∀ i : Fin r.k, r.ci i.val ≠ r.K) :
    Function.Injective (dAt r) := by
  intro u v H
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some j =>
      have h : 0=d r j.val := H
      unfold d at h
      exact (hFresh j (by omega)).elim
  | some i =>
    cases v with
    | none =>
      have h : d r i.val=0 := H
      unfold d at h
      exact (hFresh i (by omega)).elim
    | some j =>
      have he : d r i.val=d r j.val := H
      unfold d at he
      have hij : i=j := by
        by_contra h
        exact hDist i j h (by omega)
      rw [hij]

theorem actual_remaining_card (r : Row) (p : Nodes r) :
    Fintype.card (Remaining r p)=r.k := by
  classical
  let e : {x : Nodes r // x = p} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨p, rfl⟩
      left_inv := fun x => Subtype.ext x.property.symm
      right_inv := fun x => by cases x; rfl }
  have h : Fintype.card {x : Nodes r // x=p}=1 := by
    simpa only [Fintype.card_unit] using Fintype.card_congr e
  simp only [Remaining,Fintype.card_subtype_compl,h,Nodes,Fintype.card_option,Fintype.card_fin,Nat.add_sub_cancel]

theorem actual_slot_card (r : Row) (p : Nodes r) :
    Fintype.card (Slot (Remaining r p))=1+2*r.k := by
  simp only [Slot,Fintype.card_sum,Fintype.card_unit,Fintype.card_prod,Fintype.card_bool,actual_remaining_card]

theorem exact_polynomial (r : Row) (u : Nodes r) (m : ℤ) :
    PAt r m u=(dAt r u)*(r.W:ℤ)*m^2+2*(dAt r u)*r.c*m+kAt r u := by
  cases u
  · norm_num [PAt,dAt,kAt]
  · rfl

@[expose] def edgeOffset (r : Row) (p : Nodes r) (s : ℤ) (h : Bool→ℤ) :
    Slot (Remaining r p)→ℤ
  | .inl _=>0
  | .inr (e,i)=>PAt r (s+h e) i.val-PAt r (s+h e) p

theorem offset_exact (r : Row) (p : Nodes r) (s : ℤ) (h : Bool→ℤ)
    (u : Slot (Remaining r p)) :
    edgeOffset r p s h u=offset (r.W:ℤ) (dAt r p) s (fun i=>dAt r i.val)
      (fun i=>2*(dAt r i.val-dAt r p)*r.c) (fun i=>kAt r i.val-kAt r p) h u := by
  rcases u with _|⟨e,i⟩
  · rfl
  · simp only [edgeOffset,offset,exact_polynomial]
    ring

theorem actual_edge_probe (r : Row) (p : Nodes r) (s : ℤ)
    (hDist : ∀ i j : Fin r.k,i ≠ j → r.ci i.val ≠ r.ci j.val)
    (hFresh : ∀ i : Fin r.k, r.ci i.val ≠ r.K)
    (b wrap : Slot (Remaining r p)→ℤ) (x n : ℤ)
    (u v : Slot (Remaining r p)) (hne : u≠v) :
    ∃ e : Bool,∃ a : ℤ,a≠0 ∧
    a=topTag (fun i=>dAt r i.val) (dAt r p) e u-topTag (fun i=>dAt r i.val) (dAt r p) e v ∧
    qprobe (fun h=>
      ((r.W:ℤ)*(x+edgeOffset r p s h u-wrap u*n)+b u)-
        ((r.W:ℤ)*(x+edgeOffset r p s h v-wrap v*n)+b v)) e=2*(r.W:ℤ)^2*a := by
  have hI := tops_inj r hDist hFresh
  obtain ⟨e,he⟩ := distinguishes (fun i : Remaining r p=>dAt r i.val) (dAt r p)
    (fun _ _ H=>Subtype.ext (hI H)) (fun i H=>i.property (hI H)) u v hne
  refine ⟨e,_,sub_ne_zero.mpr he,rfl,?_⟩
  simp only [offset_exact]
  exact physical_probe _ _ _ _ _ _ b wrap x n u v e

end ActualTZFirstPETEdgeRows318
