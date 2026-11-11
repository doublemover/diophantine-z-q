module
public import OriginalChartZeroKernelIso318
public import IntegralLineRestriction318
public section
noncomputable section
namespace IntegralOriginalZeroKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open OriginalJointAffineFrameBasis318 SectionZeroAffineRefinement318 ModuleLocalGluing318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Z : Scheme.{u}} [IsIntegral X] (L : Line X) (s : Γ(L.object,⊤)) (hs : s≠0)

/-- Nonzero genuine sections on the original integral scheme give
injective contraction on EVERY original framed subopen, including empty
ones. The nonempty case uses the actual integral section ring. -/
lemma contraction_injective (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) :
    Function.Injective ((InverseLineSectionContraction318.hom L s).app V) := by
  classical
  by_cases hn : Nonempty V
  · letI := hn
    have hne : InverseLineSectionContraction318.coordinate L i V hV
        (res L.object (show V≤⊤ from le_top) s)≠0 := by
      intro he
      apply hs
      apply IntegralLineRestriction318.zero_of_restrict_zero L V s
      apply (InverseLineSectionContraction318.coordinate L i V hV).injective
      simpa only [map_zero] using he
    apply InverseLineSectionContraction318.injective_on_subopen L s i V hV
    intro a ha
    exact (mul_eq_zero.mp ha).resolve_right hne
  · have hbot : V=⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (hn ⟨⟨x,hx⟩⟩).elim
    intro a b _
    apply (InverseLineSectionContraction318.inverseCoordinate L i V hV).injective
    haveI : Subsingleton Γ(X,V) := by rw [hbot]; infer_instance
    exact Subsingleton.elim _ _

variable {κ : Type u} (A : κ → CommRingCat.{u}) (j : ∀ a,Spec (A a) ⟶ X)
  [∀ a,IsOpenImmersion (j a)] (hc : ⊤≤⨆a,(j a).opensRange)
  (p : Z ⟶ X) [QuasiCompact p]
  (z : ∀ a,Spec (CommRingCat.of (A a⧸sectionIdeal (A a) (j a) L s)) ⟶ Z)
  (hz : ∀ a,IsPullback (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (sectionIdeal (A a) (j a) L s)))) (z a) (j a) p)
local notation "F" => InverseLineSectionContraction318.hom L s
local notation "G" => ActualClosedIdealModule318.structure p
local notation "B" => OriginalJointAffineFrameBasis318.Index L A j

/-- The ACTUAL original zero ideal of a nonzero section on an integral
source is globally its inverse line, with original inclusion retained.
No effective-Cartier or regular-coordinate premise is assumed. -/
@[expose] def iso : (FramedLineInverse318.inverse L).object ≅ ActualClosedIdealModule318.object p :=
  ModuleBasisKernel318.iso F G (fun b : B => embedding L A j b ''ᵁ ⊤)
    (image_basis L A j hc) (OriginalChartZeroKernelIso318.exact_on_basis L s A j p z hz)
    (fun b => contraction_injective L s hs b.frame (embedding L A j b ''ᵁ ⊤)
      (OriginalJointAffineFrameBasis318.frame_le L A j b))

@[reassoc] lemma iso_inclusion : (iso L s hs A j hc p z hz).hom ≫
    ActualClosedIdealModule318.inclusion p=F :=
  ModuleBasisKernel318.iso_hom_inclusion F G (fun b : B => embedding L A j b ''ᵁ ⊤)
    (image_basis L A j hc) (OriginalChartZeroKernelIso318.exact_on_basis L s A j p z hz)
    (fun b => contraction_injective L s hs b.frame (embedding L A j b ''ᵁ ⊤)
      (OriginalJointAffineFrameBasis318.frame_le L A j b))
end IntegralOriginalZeroKernel318
