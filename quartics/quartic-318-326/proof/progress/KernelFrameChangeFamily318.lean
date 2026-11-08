module
public import KernelFrameChangeCoordinates318
public section
noncomputable section
namespace KernelFrameChangeFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KernelUniversalFrame318 F3FrameChange318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
@[expose] def frameMap (g:F3FrameChange318.Group) : Frame N ⟶ Frame N:=
  LiteralIndependentFrameChange318.map N g
@[reassoc] theorem frameMap_base (g:F3FrameChange318.Group) : frameMap N g ≫ frameBase N=frameBase N:=
  LiteralIndependentSectionAction318.map_structure N g
@[reassoc] theorem frameMap_mul (g h:F3FrameChange318.Group) : frameMap N g ≫ frameMap N h=frameMap N (g*h):=
  LiteralIndependentFrameChange318.map_mul N g h
@[simp] theorem frameMap_one : frameMap N 1=𝟙 (Frame N):=LiteralIndependentFrameChange318.map_one N
/-- Change only the actual frame, retaining the original kernel point. -/
@[expose] def map (g:F3FrameChange318.Group) : family N ⟶ family N:=
  pullback.lift (original N) (projection N ≫ frameMap N g) (by
    rw [Category.assoc,frameMap_base]
    exact pullback.condition)
@[reassoc] theorem map_original (g:F3FrameChange318.Group) : map N g ≫ original N=original N:=
  pullback.lift_fst _ _ _
@[reassoc] theorem map_projection (g:F3FrameChange318.Group) :
    map N g ≫ projection N=projection N ≫ frameMap N g:=
  pullback.lift_snd _ _ _
@[reassoc] theorem map_mul (g h:F3FrameChange318.Group) : map N g ≫ map N h=map N (g*h):=by
  apply pullback.hom_ext
  · change (map N g ≫ map N h) ≫ original N=map N (g*h) ≫ original N
    simp only [Category.assoc,map_original]
  · change (map N g ≫ map N h) ≫ projection N=map N (g*h) ≫ projection N
    simp only [Category.assoc,map_projection,map_projection_assoc,frameMap_mul]
@[simp] theorem map_one : map N 1=𝟙 (family N):=by
  apply pullback.hom_ext
  · change map N 1 ≫ original N=𝟙 (family N) ≫ original N
    rw [map_original,Category.id_comp]
  · change map N 1 ≫ projection N=𝟙 (family N) ≫ projection N
    rw [map_projection,frameMap_one,Category.comp_id,Category.id_comp]
@[expose] def iso (g:F3FrameChange318.Group) : family N ≅ family N where
  hom:=map N g
  inv:=map N g⁻¹
  hom_inv_id:=by rw [map_mul,mul_inv_cancel,map_one]
  inv_hom_id:=by rw [map_mul,inv_mul_cancel,map_one]
/-- Exact coordinate compatibility on each genuine section. -/
@[reassoc] theorem section_change (g:F3FrameChange318.Group) (c:Standard) :
    frameMap N g ≫ sectionMap N c=
      sectionMap N (g c) ≫ map N g:=by
  apply pullback.hom_ext
  · change (frameMap N g ≫ sectionMap N c) ≫ original N=
      (sectionMap N (g c) ≫ map N g) ≫ original N
    simp only [Category.assoc,section_original,map_original]
    exact KernelFrameChangeCoordinates318.combination_value N g c
  · change (frameMap N g ≫ sectionMap N c) ≫ projection N=
      (sectionMap N (g c) ≫ map N g) ≫ projection N
    rw [Category.assoc,section_projection,Category.comp_id,Category.assoc,map_projection,
      ←Category.assoc,section_projection,Category.id_comp]
/-- If the actual kernel point is kept fixed, coefficients change by
exactly g inverse when the actual frame changes by g. -/
@[reassoc] theorem section_inverse_coordinates (g:F3FrameChange318.Group) (c:Standard) :
    sectionMap N c ≫ map N g=frameMap N g ≫ sectionMap N (g⁻¹ c):=by
  have h:=section_change N g (g⁻¹ c)
  simpa only [LinearEquiv.coe_inv,LinearEquiv.apply_symm_apply] using h.symm
end KernelFrameChangeFamily318
