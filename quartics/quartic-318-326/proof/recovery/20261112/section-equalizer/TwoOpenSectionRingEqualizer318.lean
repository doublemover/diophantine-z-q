module
public import TwoOpenSectionRingUniversal318
public section
noncomputable section
namespace TwoOpenSectionRingEqualizer318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {U V X N : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b]
variable (l : N ⟶ U) (r : N ⟶ V) (H : IsPullback l r a b)
open TwoOpenSourceUnion318
abbrev pairs : Subring (Γ(U,⊤) × Γ(V,⊤)) :=
  RingHom.eqLocus (l.appTop.hom.comp (RingHom.fst _ _))
    (r.appTop.hom.comp (RingHom.snd _ _))
def fst : pairs l r →+* Γ(U,⊤) := (RingHom.fst _ _).comp (pairs l r).subtype
def snd : pairs l r →+* Γ(V,⊤) := (RingHom.snd _ _).comp (pairs l r).subtype
lemma compatible : CommRingCat.ofHom (fst l r)≫l.appTop=
    CommRingCat.ofHom (snd l r)≫r.appTop := by
  ext z
  exact z.property
/-- Literal restriction of every whole regular section to BOTH charts. -/
def restriction : Γ(scheme a b,⊤) →+* pairs l r :=
  ((left a b).appTop.hom.prod (right a b).appTop.hom).codRestrict _ (by
    intro z
    have h : l≫left a b=r≫right a b := by
      apply (cancel_mono (opens a b).ι).mp
      simpa only [Category.assoc,left_into,right_into] using H.w
    have hh := congrArg (fun k : N ⟶ scheme a b => k.appTop.hom z) h
    simpa only [Scheme.Hom.comp_appTop] using hh)
def glue : pairs l r →+* Γ(scheme a b,⊤) :=
  (TwoOpenSectionRingUniversal318.lift a b l r H (CommRingCat.of (pairs l r))
    (CommRingCat.ofHom (fst l r)) (CommRingCat.ofHom (snd l r)) (compatible l r)).hom
lemma glue_left (z : pairs l r) : (left a b).appTop.hom (glue a b l r H z)=z.val.1 :=
  congrArg (fun k => k.hom z) (TwoOpenSectionRingUniversal318.lift_left a b l r H _ _ _ _)
lemma glue_right (z : pairs l r) : (right a b).appTop.hom (glue a b l r H z)=z.val.2 :=
  congrArg (fun k => k.hom z) (TwoOpenSectionRingUniversal318.lift_right a b l r H _ _ _ _)
lemma restrict_glue (z : pairs l r) : restriction a b l r H (glue a b l r H z)=z := by
  apply Subtype.ext
  exact Prod.ext (glue_left a b l r H z) (glue_right a b l r H z)
lemma glue_restrict : (glue a b l r H).comp (restriction a b l r H)=RingHom.id _ := by
  have hh : CommRingCat.ofHom ((glue a b l r H).comp (restriction a b l r H))=
      CommRingCat.ofHom (RingHom.id Γ(scheme a b,⊤)) := by
    apply TwoOpenSectionRingUniversal318.hom_ext a b (CommRingCat.of Γ(scheme a b,⊤))
    · ext z
      exact glue_left a b l r H (restriction a b l r H z)
    · ext z
      exact glue_right a b l r H (restriction a b l r H z)
  exact congrArg (fun k => k.hom) hh
/-- Actual whole Γ is the FULL compatible-pair ring, not merely its
image in a fraction field. Empty charts and nilpotents are retained. -/
def equivalence : Γ(scheme a b,⊤) ≃+* pairs l r where
  __ := restriction a b l r H
  invFun := glue a b l r H
  left_inv z := DFunLike.congr_fun (glue_restrict a b l r H) z
  right_inv := restrict_glue a b l r H
end TwoOpenSectionRingEqualizer318
