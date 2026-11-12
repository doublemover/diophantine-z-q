module
public import ActualTwoDescentIntegralRationalRegularSections318
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public section
noncomputable section
namespace ActualTwoDescentProperClosedFieldConstants318
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
/-- Literal structural map, including the native Spec/global-section
comparison. The proof does NOT assume geometric integrality. -/
def structural : K →+* Γ(X,⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
lemma integral : (structural p).IsIntegral :=
  (RingHom.isIntegral_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective).trans _ _
      (isIntegral_appTop_of_universallyClosed p)
/-- Proper integral over an algebraically CLOSED base gives every
actual global function as a unique base constant. Geometric integrality
is neither silently inferred nor supplied as a new hypothesis. -/
lemma bijective : Function.Bijective (structural p) :=
  IsAlgClosed.ringHom_bijective_of_isIntegral (structural p) (integral p)
lemma units (s : Γ(X,⊤)ˣ) : ∃! c : Kˣ,structural p (c:K)=(s:Γ(X,⊤)) := by
  obtain ⟨c,hc⟩ := (bijective p).surjective (s:Γ(X,⊤))
  have hn : c≠0 := by
    intro h
    apply s.ne_zero
    rw [←hc,h,map_zero]
  refine ⟨Units.mk0 c hn,hc,?_⟩
  intro d hd
  apply Units.ext
  exact (bijective p).injective (hd.trans hc.symm)

end ActualTwoDescentProperClosedFieldConstants318
