module
public import FlatBinarySectionAlgebra318
public section
noncomputable section
namespace TwoOpenSectionAlgebraEqualizer318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
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
include H hs ht hf hg in
lemma compatible (z : Γ(scheme a b,⊤)) : f (s z)=g (t z) := by
  change f.toRingHom (s.toRingHom z)=g.toRingHom (t.toRingHom z)
  rw [hs,ht,hf,hg]
  exact (TwoOpenSectionRingEqualizer318.restriction a b l r H z).property
def restriction : Γ(scheme a b,⊤) →ₐ[R] FlatBinarySectionAlgebra318.pairs f g :=
  (s.prod t).codRestrict _ (compatible a b l r H s t f g hs ht hf hg)
include hs ht hf hg in
lemma bijective : Function.Bijective (restriction a b l r H s t f g hs ht hf hg) := by
  constructor
  · intro x y h
    apply (TwoOpenSectionRingEqualizer318.equivalence a b l r H).injective
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change (s.toRingHom x,t.toRingHom x)=(s.toRingHom y,t.toRingHom y) at hh
    simpa only [hs,ht] using hh
  · intro z
    have hz : l.appTop.hom z.val.1=r.appTop.hom z.val.2 := by
      rw [←hf,←hg]
      exact z.property
    obtain ⟨w,hw⟩ := (TwoOpenSectionRingEqualizer318.equivalence a b l r H).surjective ⟨z.val,hz⟩
    refine ⟨w,Subtype.ext ?_⟩
    have hh := congrArg Subtype.val hw
    change (s.toRingHom w,t.toRingHom w)=z.val
    simpa only [hs,ht] using hh
/-- The genuine whole section ring and its coefficient action, not
an abstract replacement with a newly chosen multiplication. -/
def equivalence : Γ(scheme a b,⊤) ≃ₐ[R] FlatBinarySectionAlgebra318.pairs f g :=
  AlgEquiv.ofBijective (restriction a b l r H s t f g hs ht hf hg)
    (bijective a b l r H s t f g hs ht hf hg)
end TwoOpenSectionAlgebraEqualizer318
