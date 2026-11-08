module
public import KernelFrameChangeFamily318
public import KernelUniversalTrivialization318
public section
noncomputable section
namespace KernelFrameChangeEquivariance318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KernelUniversalFrame318 F3FrameChange318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
/-- Actual change of coefficients on the disjoint union model:
(c,frame) maps to (g inverse c,frame.g). -/
@[expose] def coproductMap (g:F3FrameChange318.Group) :
    (∐ fun _ : Standard=>Frame N) ⟶ (∐ fun _ : Standard=>Frame N):=
  Sigma.desc (fun c:Standard=>KernelFrameChangeFamily318.frameMap N g ≫
    Sigma.ι (fun _ : Standard=>Frame N) (g⁻¹ c))
@[reassoc] theorem component (g:F3FrameChange318.Group) (c:Standard) :
    Sigma.ι (fun _ : Standard=>Frame N) c ≫ coproductMap N g=
      KernelFrameChangeFamily318.frameMap N g ≫ Sigma.ι (fun _ : Standard=>Frame N) (g⁻¹ c):=
  Sigma.ι_comp_desc _ _
variable [NeZero N]
/-- Exact universal-kernel trivialization equivariance, on all Scheme
structure including nilpotents, with the original kernel point fixed. -/
@[reassoc] theorem equivariant (g:F3FrameChange318.Group) :
    coproductMap N g ≫ (KernelUniversalTrivialization318.iso N).hom=
      (KernelUniversalTrivialization318.iso N).hom ≫ KernelFrameChangeFamily318.map N g:=by
  apply Sigma.hom_ext
  intro c
  rw [component_assoc,KernelUniversalTrivialization318.component,
    KernelUniversalTrivialization318.component_assoc]
  exact (KernelFrameChangeFamily318.section_inverse_coordinates N g c).symm
/-- Both inverse witnesses are inherited from explicit actual family and
universal-trivialization isomorphisms, not from coefficient labels alone. -/
@[expose] def iso (g:F3FrameChange318.Group) :
    (∐ fun _ : Standard=>Frame N) ≅ (∐ fun _ : Standard=>Frame N):=
  KernelUniversalTrivialization318.iso N ≪≫ KernelFrameChangeFamily318.iso N g ≪≫
    (KernelUniversalTrivialization318.iso N).symm
@[simp] theorem iso_hom (g:F3FrameChange318.Group) : (iso N g).hom=coproductMap N g:=by
  apply (cancel_mono (KernelUniversalTrivialization318.iso N).hom).mp
  rw [equivariant]
  simp only [iso,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rfl
@[reassoc] theorem original_point_fixed (g:F3FrameChange318.Group) :
    coproductMap N g ≫ (KernelUniversalTrivialization318.iso N).hom ≫ original N=
      (KernelUniversalTrivialization318.iso N).hom ≫ original N:=by
  rw [equivariant_assoc,KernelFrameChangeFamily318.map_original]
end KernelFrameChangeEquivariance318
