module
public import OriginalGlobalFrameTransport318
public import OriginalArithmeticTensorFiber318
public section
noncomputable section
namespace OriginalIntrinsicPointModule318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry CategoryTheory
open OriginalPointSheafSectionValues318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)

/-- The SINGLE genuine K-line obtained by global sections of the actual
whole-point pullback of the original proper-curve tensor sheaf.
Neither this object nor its canonical section element has a branch index. -/
abbrev pointModule := moduleSpecΓFunctor.obj (OriginalGlobalPointTensorSheaf318.pointSheaf c t)

@[expose] def unitFrame {F : Type*} [Field F] :
    moduleSpecΓFunctor.obj (SheafOfModules.unit (Spec (CommRingCat.of F)).ringCatSheaf) ≃ₗ[F] F where
  toFun := (Scheme.ΓSpecIso (CommRingCat.of F)).hom
  invFun := (Scheme.ΓSpecIso (CommRingCat.of F)).inv
  left_inv x := Iso.hom_inv_id_apply _ x
  right_inv x := Iso.inv_hom_id_apply _ x
  map_add' x y := map_add _ x y
  map_smul' a x := by
    change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a*x)=a*(Scheme.ΓSpecIso (CommRingCat.of F)).hom x
    rw [map_mul,Iso.inv_hom_id_apply]

@[expose] def frame (i : Fin 4) : pointModule c t ≃ₗ[K c t] K c t :=
  (moduleSpecΓFunctor.mapIso (pointFrame c t hn i)).toLinearEquiv ≪≫ₗ unitFrame
lemma frame_apply (i : Fin 4) (x : pointModule c t) :
    frame c t hn i x=(Scheme.ΓSpecIso (CommRingCat.of (K c t))).hom
      ((pointFrame c t hn i).hom.app ⊤ x) := rfl

@[expose] def globalElement (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) : pointModule c t :=
  (pulledSection c t s).app ⊤ (show Γ(Spec (CommRingCat.of (K c t)),⊤) from 1)

/-- Normalization of the canonical pulled section at the actual point,
now in the genuine K-module rather than just its sheaf presentation. -/
lemma frame_global (i : Fin 4) (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    frame c t hn i (globalElement c t s)=ContactBicanonicalPointValue318.value c t hn i s := by
  rw [frame_apply]
  have h := congrArg (fun φ => φ.app ⊤ (show Γ(Spec (CommRingCat.of (K c t)),⊤) from 1))
    (pulledSection_frame c t hn i s)
  change (pointFrame c t hn i).hom.app ⊤ (globalElement c t s)=_ at h
  rw [ClutchedModule318.multiply_top,one_mul] at h
  rw [h,Iso.inv_hom_id_apply]

lemma frame_transition (i j : Fin 4) (x : pointModule c t) :
    frame c t hn j x=ContactBicanonicalPointHeight318.frameScalar c t hn i j*frame c t hn i x := by
  have h := congrArg (fun φ => (pointFrame c t hn i).hom≫φ)
    (OriginalGlobalFrameTransport318.pointFrame_transition c t hn i j)
  simp only [←Category.assoc,Iso.hom_inv_id,Category.id_comp] at h
  have hx := congrArg (fun φ => φ.app ⊤ x) h
  change (pointFrame c t hn j).hom.app ⊤ x=
    (ClutchedModule318.multiply ((Scheme.ΓSpecIso (CommRingCat.of (K c t))).inv
      (ContactBicanonicalPointHeight318.frameScalar c t hn i j))).app ⊤
      ((pointFrame c t hn i).hom.app ⊤ x) at hx
  rw [ClutchedModule318.multiply_top] at hx
  rw [frame_apply,frame_apply,hx,map_mul,Iso.inv_hom_id_apply,mul_comm]

/-- Both-inverse actual comparison with the branch algebraic tensor
fiber. EVERY canonical global section has the already proved fiber. -/
@[expose] def toArithmeticFiber (i : Fin 4) : pointModule c t ≃ₗ[K c t]
    OriginalArithmeticTensorFiber318.fiber c t hn i :=
  frame c t hn i ≪≫ₗ (OriginalArithmeticTensorFiber318.frame c t hn i).symm
lemma toArithmeticFiber_global (i : Fin 4) (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    toArithmeticFiber c t hn i (globalElement c t s)=OriginalArithmeticTensorFiber318.globalFiber c t hn i s := by
  apply (OriginalArithmeticTensorFiber318.frame c t hn i).injective
  change OriginalArithmeticTensorFiber318.frame c t hn i
    ((OriginalArithmeticTensorFiber318.frame c t hn i).symm (frame c t hn i _))=_
  rw [LinearEquiv.apply_symm_apply,frame_global,OriginalArithmeticTensorFiber318.frame_globalFiber]
end OriginalIntrinsicPointModule318
