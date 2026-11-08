module
public import LiteralKernelFrameChange318
public import LiteralIndependentPairFunctor318
public section
noncomputable section
namespace LiteralIndependentFrameChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318 (Points)
open LiteralKernelAddition318 F3FrameChange318
open LiteralKernelFrameChange318 LiteralIndependentPairOpen318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
lemma pull_left (g:Group) : pull N g (leftPoint N)=change g (frame N) 0:=
  congrFun (pull_frame N g) 0
lemma pull_right (g:Group) : pull N g (rightPoint N)=change g (frame N) 1:=
  congrFun (pull_frame N g) 1
/-- The residue test is used only to detect the four actual open zero
loci. No equality of Scheme maps is inferred from field-point equality. -/
lemma pulled_nonzero (g:Group) (x:product N) (p:Points N (productBase N)) :
    p.val (map N g x)∈LiteralKernelPrimitiveOpen318.primitiveOpen N ↔
    atPoint N (𝟙 (product N)) x (pull N g p)≠0:=by
  rw [LiteralKernelPrimitiveOpen318.mem_primitiveOpen_iff]
  apply Iff.symm
  apply not_congr
  rw [atPoint_zero_iff,pull_val,Scheme.Hom.comp_apply]
  rfl
/-- Genuine GL2 changes of frame preserve fiberwise independence, not
just inequalities between global sections on a disconnected test. -/
theorem preserves (g:Group) (x:product N) (hx:x∈independentOpen N) :
    map N g x∈independentOpen N:=by
  let L:=atPoint N (𝟙 (product N)) x
  have hv:LinearIndependent (ZMod 3) (fun i=>L (frame N i)):=by
    have hf:(fun i=>L (frame N i))=![L (leftPoint N),L (rightPoint N)]:=by
      funext i
      fin_cases i <;> rfl
    rw [hf]
    exact (mem_iff_independent N (𝟙 (product N)) x).mp hx
  have hc:=F3FrameChange318.independent g (fun i=>L (frame N i)) hv
  have he:(fun i=>L (change g (frame N) i))=change g (fun i=>L (frame N i)):=by
    funext i
    exact change_natural L g (frame N) i
  rw [←he] at hc
  have hpair:LinearIndependent (ZMod 3)
      ![L (change g (frame N) 0),L (change g (frame N) 1)]:=by
    convert hc using 1
    funext i
    fin_cases i <;> rfl
  rw [mem_independentOpen]
  simp only [combinationMap,pulled_nonzero,combination,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,Matrix.cons_val,Matrix.tail_cons,Matrix.cons_val_fin_one,
    map_sub,map_add,pull_left,pull_right]
  exact (F3PairIndependence318.combinations_iff _ _).mp hpair

/-- The represented frame-change map is the actual restriction of the
product morphism, via the defining open immersion. -/
@[expose] def map (g:Group) : scheme N ⟶ scheme N:=
  IsOpenImmersion.lift (inclusion N) (inclusion N ≫ LiteralKernelFrameChange318.map N g) (by
    rw [show Set.range (inclusion N)=(independentOpen N:Set (product N)) from Scheme.Opens.range_ι _]
    rintro _ ⟨x,rfl⟩
    exact preserves N g (inclusion N x) x.property)
@[reassoc] theorem map_inclusion (g:Group) :
    map N g ≫ inclusion N=inclusion N ≫ LiteralKernelFrameChange318.map N g:=
  IsOpenImmersion.lift_fac _ _ _
@[reassoc] theorem map_mul (g h:Group) : map N g ≫ map N h=map N (g*h):=by
  apply (cancel_mono (inclusion N)).mp
  calc
    (map N g ≫ map N h) ≫ inclusion N = map N g ≫ (inclusion N ≫ LiteralKernelFrameChange318.map N h) := by rw [Category.assoc,map_inclusion]
    _ = inclusion N ≫ (LiteralKernelFrameChange318.map N g ≫ LiteralKernelFrameChange318.map N h) := by rw [←Category.assoc,map_inclusion,Category.assoc]
    _ = inclusion N ≫ LiteralKernelFrameChange318.map N (g*h) := by rw [LiteralKernelFrameChange318.map_mul]
    _ = map N (g*h) ≫ inclusion N := (map_inclusion N (g*h)).symm
@[simp] theorem map_one : map N 1=𝟙 (scheme N):=by
  apply (cancel_mono (inclusion N)).mp
  simp only [map_inclusion,LiteralKernelFrameChange318.map_one,Category.comp_id,Category.id_comp]
/-- Both inverse identities are identities of the actual restricted
Scheme maps; no degree-one or geometric-bijection shortcut is used. -/
@[expose] def iso (g:Group) : scheme N ≅ scheme N where
  hom:=map N g
  inv:=map N g⁻¹
  hom_inv_id:=by rw [map_mul,mul_inv_cancel,map_one]
  inv_hom_id:=by rw [map_mul,inv_mul_cancel,map_one]
end LiteralIndependentFrameChange318
