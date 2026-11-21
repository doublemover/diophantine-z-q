module
public import ActualTZSharedFineHybridStencil318
public section
noncomputable section
namespace ActualTZSharedFineHybridProbes318
open scoped BigOperators
open ActualTZSharedFineHybridStencil318

variable {a t b s : ℕ}

@[expose] def globalNeedle (i : Fin a) : Vals a t b s
  | .inl (e,j)=>if j=i ∧ e=true then 1 else 0
  | .inr _=>0

@[expose] def localNeedle (r : Fin t) (j : Fin b) (k : Fin s) : Vals a t b s
  | .inl _=>0
  | .inr (u,.inl l)=>if u=r ∧ l=k then 1 else 0
  | .inr (u,.inr (i,e))=>if u=r ∧ i=j ∧ e=true then 1 else 0

theorem zero (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b) :
    off q A w (fun _=>0)=0 := by
  simp only [off,sub_self,mul_zero,ite_self,Finset.sum_const_zero,add_zero]

theorem global (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b) (i : Fin a) :
    off q A w (globalNeedle i)=if w (.inl i) then (q:ℤ) else 0 := by
  have h0 : (∑ p : Fin t×Fin b,if w (.inr p) then
      (∑ k : Fin s,A p.2 k*globalNeedle (b:=b) i (hpos (b:=b) p.1 k))*
        (globalNeedle (s:=s) i (lpos (s:=s) p.1 p.2 true)-
          globalNeedle (s:=s) i (lpos (s:=s) p.1 p.2 false)) else 0)=0 := by
    simp only [globalNeedle,lpos,sub_self,mul_zero,ite_self,Finset.sum_const_zero]
  unfold off
  rw [h0,add_zero,Finset.sum_eq_single i]
  · have hTrue : globalNeedle (t:=t) (b:=b) (s:=s) i (gpos i true)=1 := by
      simp [globalNeedle,gpos]
    have hFalse : globalNeedle (t:=t) (b:=b) (s:=s) i (gpos i false)=0 := by
      simp [globalNeedle,gpos]
    simp only [hTrue,hFalse,sub_zero,mul_one]
  · intro j _ hj
    simp only [globalNeedle,gpos,hj,false_and,if_false,sub_self,mul_zero,ite_self]
  · simp

private theorem local_delta (r u : Fin t) (j i : Fin b) (k : Fin s) :
    localNeedle (a:=a) r j k (lpos u i true)-localNeedle (a:=a) r j k (lpos u i false)=
      if (u,i)=(r,j) then 1 else 0 := by
  by_cases h : (u,i)=(r,j)
  · have hu : u=r := congrArg Prod.fst h
    have hi : i=j := congrArg Prod.snd h
    subst u
    subst i
    simp [localNeedle,lpos]
  · have hab : ¬(u=r ∧ i=j) := fun h' => h (Prod.ext h'.1 h'.2)
    simp [localNeedle,lpos,h,hab]

private theorem hsum (A : Fin b→Fin s→ℤ) (r : Fin t) (j : Fin b) (k : Fin s) :
    (∑ i : Fin s,A j i*localNeedle (a:=a) r j k (hpos r i))=A j k := by
  rw [Finset.sum_eq_single k]
  · simp [localNeedle,hpos]
  · intro i _ hi
    simp only [localNeedle,hpos,hi,and_false,if_false,mul_zero]
  · simp

/-- Needle at (r,k) and (r,j,true). Every other axis in that
SAME r block sees h_{r,k}=1 too, but its endpoint difference is
zero, so only axis j contributes. This is the valid shared-fine
probe, not an independent fine copy indexed by j. -/
theorem local_axis (q : ℕ) (A : Fin b→Fin s→ℤ) (w : Bits a t b)
    (r : Fin t) (j : Fin b) (k : Fin s) :
    off q A w (localNeedle r j k)=if w (.inr (r,j)) then A j k else 0 := by
  have h0 : (∑ i : Fin a,if w (.inl i) then (q:ℤ)*
      (localNeedle r j k (gpos i true)-localNeedle r j k (gpos i false)) else 0)=0 := by
    simp only [localNeedle,gpos,sub_self,mul_zero,ite_self,Finset.sum_const_zero]
  unfold off
  rw [h0,zero_add,Finset.sum_eq_single (r,j)]
  · have h : localNeedle (a:=a) r j k (lpos r j true)-
        localNeedle (a:=a) r j k (lpos r j false)=1 := by
      simpa using local_delta (a:=a) r r j j k
    simp only [h,hsum,mul_one]
  · intro p _ hp
    have h := local_delta (a:=a) r p.1 j p.2 k
    simp only [if_neg hp] at h
    simp only [h,mul_zero,ite_self]
  · simp

end ActualTZSharedFineHybridProbes318
