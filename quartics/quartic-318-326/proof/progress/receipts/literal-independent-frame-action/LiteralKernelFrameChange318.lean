module
public import F3FrameChange318
public import LiteralKernelPointBaseTransport318
public section
noncomputable section
namespace LiteralKernelFrameChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318 LiteralKernelAddition318 F3FrameChange318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
@[expose] def frame : Fin 2→Points N (productBase N):=![leftPoint N,rightPoint N]
/-- Actual product morphism specified by the two genuine F3 linear
combinations. It uses no enumeration of geometric kernel points. -/
@[expose] def map (g:Group) : product N ⟶ product N:=
  pair N (productBase N) (change g (frame N) 0) (change g (frame N) 1)
@[reassoc] theorem map_fst (g:Group) : map N g ≫ pullback.fst _ _=(change g (frame N) 0).val:=
  pair_fst N _ _ _
@[reassoc] theorem map_snd (g:Group) : map N g ≫ pullback.snd _ _=(change g (frame N) 1).val:=
  pair_snd N _ _ _
@[reassoc] theorem map_base (g:Group) : map N g ≫ productBase N=productBase N:=by
  rw [productBase,map_fst_assoc]
  exact (change g (frame N) 0).property
@[expose] def pull (g:Group) : Points N (productBase N) →ₗ[ZMod 3] Points N (productBase N):=
  LiteralKernelPointBaseTransport318.pull N (map N g) (productBase N) (productBase N) (map_base N g)
@[simp] theorem pull_val (g:Group) (p:Points N (productBase N)) :
    (pull N g p).val=map N g ≫ p.val:=LiteralKernelPointBaseTransport318.pull_val _ _ _ _ _ _
lemma pull_frame (g:Group) : (fun i=>pull N g (frame N i))=change g (frame N):=by
  funext i
  apply Subtype.ext
  rw [pull_val]
  fin_cases i
  · exact map_fst N g
  · exact map_snd N g
lemma pull_change (g h:Group) (i:Fin 2) :
    pull N g (change h (frame N) i)=change (g*h) (frame N) i:=by
  rw [change_natural,pull_frame,change_mul]
/-- Scheme composition has the declared right-frame convention. -/
@[reassoc] theorem map_mul (g h:Group) : map N g ≫ map N h=map N (g*h):=by
  apply pullback.hom_ext
  · rw [Category.assoc,map_fst,map_fst]
    simpa only [pull_val] using congrArg Subtype.val (pull_change N g h 0)
  · rw [Category.assoc,map_snd,map_snd]
    simpa only [pull_val] using congrArg Subtype.val (pull_change N g h 1)
@[simp] theorem map_one : map N 1=𝟙 (product N):=by
  apply pullback.hom_ext
  · simp only [map_fst,change_one,frame,Matrix.cons_val_zero,Category.id_comp]
    rfl
  · simp only [map_snd,change_one,frame,Matrix.cons_val_one,Matrix.head_cons,Category.id_comp]
    rfl
/-- Explicit ambient automorphism, with both actual composite identities. -/
@[expose] def iso (g:Group) : product N ≅ product N where
  hom:=map N g
  inv:=map N g⁻¹
  hom_inv_id:=by rw [map_mul,mul_inv_cancel,map_one]
  inv_hom_id:=by rw [map_mul,inv_mul_cancel,map_one]
end LiteralKernelFrameChange318
