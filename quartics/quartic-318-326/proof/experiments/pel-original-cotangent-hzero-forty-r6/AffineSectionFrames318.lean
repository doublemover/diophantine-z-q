module
public import AffineCokernelSections318
public import FramedCokernelQuotient318
public import NormalizationChart318
public section
noncomputable section
namespace AffineSectionFrames318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {S : Type u} [CommRing S] {X : Scheme.{u}}
  (j : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion j]

/-- The original affine scalar identification, including both actual
Spec global sections and the actual open-immersion restriction inverse. -/
@[expose] def scalars : S ≃+* Γ(X,j ''ᵁ ⊤) :=
  (NormalizationChart318.targetSections j).symm.commRingCatIsoToRingEquiv

lemma smul_sections (A : X.Modules) (a : S)
    (z : moduleSpecΓFunctor.obj (A.restrict j)) :
    a • z = (scalars j a) • (show Γ(A,j ''ᵁ ⊤) from z) := by
  change ((j.appIso ⊤).inv
    ((Spec (CommRingCat.of S)).presheaf.map (𝟙 (op ⊤))
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a))) • z = _
  rw [Functor.map_id]
  rfl

/-- An ambient frame is transported with the ACTUAL scalar equivalence
into a frame of the actual affine section functor. -/
@[expose] def frame (A : X.Modules)
    (e : Γ(X,j ''ᵁ ⊤) ≃ₗ[Γ(X,j ''ᵁ ⊤)] Γ(A,j ''ᵁ ⊤)) :
    S ≃ₗ[S] moduleSpecΓFunctor.obj (A.restrict j) where
  toFun a := e (scalars j a)
  invFun z := (scalars j).symm (e.symm z)
  left_inv a := by simp only [LinearEquiv.symm_apply_apply,RingEquiv.symm_apply_apply]
  right_inv z := by simp only [RingEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  map_add' a b := by rw [map_add,map_add]
  map_smul' a b := by
    rw [smul_sections]
    change e (scalars j (a*b)) = (scalars j a) • e (scalars j b)
    rw [map_mul]
    exact e.map_smul _ _

lemma frame_symm_unit (A : X.Modules)
    (e : Γ(X,j ''ᵁ ⊤) ≃ₗ[Γ(X,j ''ᵁ ⊤)] Γ(A,j ''ᵁ ⊤))
    (z : Γ(A,j ''ᵁ ⊤)) (hz : IsUnit (e.symm z)) :
    IsUnit ((frame j A e).symm z) :=
  hz.map (scalars j).symm.toRingHom

/-- Exact actual section quotient comparison, with the full original
ring scalar square and actual section-map action retained. -/
@[expose] def quotientEquiv {A B : X.Modules} (a : A ⟶ B)
    (e : Γ(X,j ''ᵁ ⊤) ≃ₗ[Γ(X,j ''ᵁ ⊤)] Γ(A,j ''ᵁ ⊤))
    (f : Γ(X,j ''ᵁ ⊤) ≃ₗ[Γ(X,j ''ᵁ ⊤)] Γ(B,j ''ᵁ ⊤))
    (s : Γ(A,j ''ᵁ ⊤)) (t : Γ(B,j ''ᵁ ⊤)) (c : S)
    (h : a.app (j ''ᵁ ⊤) s = (scalars j c) • t)
    (hs : IsUnit (e.symm s)) (ht : IsUnit (f.symm t)) :
    AffineCokernelSections318.sectionQuotient ((Scheme.Modules.restrictFunctor j).map a)
      ≃ₗ[S] S ⧸ Ideal.span {c} :=
  FramedCokernelQuotient318.quotientEquiv (frame j A e) (frame j B f)
    (moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor j).map a)).hom
    s t c (by
      rw [smul_sections]
      exact h) (frame_symm_unit j A e s hs) (frame_symm_unit j B f t ht)
end AffineSectionFrames318
