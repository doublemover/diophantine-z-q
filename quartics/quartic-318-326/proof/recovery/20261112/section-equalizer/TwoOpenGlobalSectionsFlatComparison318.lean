module
public import TwoOpenSectionAlgebraEqualizer318
public section
noncomputable section
namespace TwoOpenGlobalSectionsFlatComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {U V X N : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b]
variable (l : N ⟶ U) (r : N ⟶ V) (H : IsPullback l r a b)
open TwoOpenSourceUnion318
variable {R : Type u} [CommRing R]
  [Algebra R Γ(scheme a b,⊤)] [Algebra R Γ(U,⊤)]
  [Algebra R Γ(V,⊤)] [Algebra R Γ(N,⊤)]
variable (s : Γ(scheme a b,⊤) →ₐ[R] Γ(U,⊤)) (t : Γ(scheme a b,⊤) →ₐ[R] Γ(V,⊤))
  (f : Γ(U,⊤) →ₐ[R] Γ(N,⊤)) (g : Γ(V,⊤) →ₐ[R] Γ(N,⊤))
  (hs : s.toRingHom=(left a b).appTop.hom) (ht : t.toRingHom=(right a b).appTop.hom)
  (hf : f.toRingHom=l.appTop.hom) (hg : g.toRingHom=r.appTop.hom)
variable (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
/-- Genuine flat global-section reconstruction in the full tensor
chart equalizer. The next geometric join must identify those chart
rings with the actual basechanged source, not a finite ambient envelope. -/
def equivalence : A ⊗[R] Γ(scheme a b,⊤) ≃ₐ[A]
    FlatBinarySectionAlgebra318.pairs (TensorAlgebraBaseChange318.map A f)
      (TensorAlgebraBaseChange318.map A g) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl A A)
    (TwoOpenSectionAlgebraEqualizer318.equivalence a b l r H s t f g hs ht hf hg)).trans
      (FlatBinarySectionAlgebra318.equivalence A f g)
@[simp] lemma pure_value (c : A) (z : Γ(scheme a b,⊤)) :
    (equivalence a b l r H s t f g hs ht hf hg A (c ⊗ₜ[R] z)).val=
      (c ⊗ₜ[R] (left a b).appTop.hom z,c ⊗ₜ[R] (right a b).appTop.hom z) := by
  change (c ⊗ₜ[R] s.toRingHom z,c ⊗ₜ[R] t.toRingHom z)=_
  rw [hs,ht]
/-- Both chart restrictions determine the ENTIRE comparison, not only
its reduced/rational image. -/
lemma unique (q : A ⊗[R] Γ(scheme a b,⊤) →ₐ[A]
    FlatBinarySectionAlgebra318.pairs (TensorAlgebraBaseChange318.map A f)
      (TensorAlgebraBaseChange318.map A g))
    (hq : ∀ c z, (q (c ⊗ₜ[R] z)).val=
      (c ⊗ₜ[R] (left a b).appTop.hom z,c ⊗ₜ[R] (right a b).appTop.hom z)) :
    q=(equivalence a b l r H s t f g hs ht hf hg A).toAlgHom := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro c z
  apply Subtype.ext
  exact (hq c z).trans (pure_value a b l r H s t f g hs ht hf hg A c z).symm
end TwoOpenGlobalSectionsFlatComparison318
