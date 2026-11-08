module
public import LiteralKernelFunctor318
public section
noncomputable section
namespace KernelPairSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318 LiteralKernelAddition318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N : ℕ) {X : Scheme}
variable (b : X ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
/-- Actual sections of the two-kernel product over the specified base map. -/
abbrev Sections := {f : X ⟶ product N // f ≫ productBase N = b}
/-- Actual linear pullback of kernel points, with only the proved base equation substituted. -/
@[expose] def restrict (f : X ⟶ product N) (hf : f ≫ productBase N = b) :
    Points N (productBase N) →ₗ[ZMod 3] Points N b := by
  subst b
  exact LiteralKernelFunctor318.precomposeLinear N (productBase N) f
@[simp] theorem restrict_val (f : X ⟶ product N) (hf : f ≫ productBase N = b)
    (p : Points N (productBase N)) : (restrict N b f hf p).val = f ≫ p.val := by
  subst b
  rfl
@[expose] def left (s : Sections N b) : Points N b := restrict N b s.val s.property (leftPoint N)
@[expose] def right (s : Sections N b) : Points N b := restrict N b s.val s.property (rightPoint N)
@[simp] theorem left_val (s : Sections N b) :
    (left N b s).val = s.val ≫ pullback.fst (structureMap N) (structureMap N) := by
  exact restrict_val N b s.val s.property (leftPoint N)
@[simp] theorem right_val (s : Sections N b) :
    (right N b s).val = s.val ≫ pullback.snd (structureMap N) (structureMap N) := by
  exact restrict_val N b s.val s.property (rightPoint N)
/-- Both explicit inverse maps use the actual product projections and pullback lift. -/
@[expose] def equiv : Sections N b ≃ Points N b × Points N b where
  toFun s := (left N b s,right N b s)
  invFun p := ⟨pair N b p.1 p.2,by rw [productBase,pair_fst_assoc,p.1.property]⟩
  left_inv s := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pair_fst,left_val]
    · rw [pair_snd,right_val]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      rw [left_val,pair_fst]
    · apply Subtype.ext
      rw [right_val,pair_snd]
end KernelPairSections318
