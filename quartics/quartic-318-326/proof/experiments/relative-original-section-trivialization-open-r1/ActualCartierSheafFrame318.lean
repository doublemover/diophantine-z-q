module
public import ActualCartierLocalGenerator318
public import LineSheafClass318
public section
noncomputable section
namespace ActualCartierSheafFrame318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineQuotientKernelSections318 ActualCartierLocalGenerator318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (A : CommRingCat.{u}) (j : Spec A ⟶ X) [IsOpenImmersion j] (c : A)
  (z : Spec (CommRingCat.of (A ⧸ Ideal.span {c})) ⟶ Z)
  (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j p)
  (hc : ∀ a : A,a*c=0 → a=0)
local notation "U" => (chartOpen A j).1

/-- The original Cartier generator is an isomorphism of ACTUAL sheaves,
proved on the complete affine basis of the whole open subscheme. -/
lemma hom_isIso : IsIso (hom p A j c z hs hc) := by
  let F := SheafOfModules.toSheaf U.toScheme.ringCatSheaf
  have hf : IsIso (F.map (hom p A j c z hs hc)) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun V : U.toScheme.affineOpens => V.1)
    · convert! U.toScheme.isBasis_affineOpens using 1
      exact Subtype.range_coe_subtype
    · intro V
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact hom_bijective p A j c z hs hc V
  letI := hf
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  exact (inferInstance : IsIso ((F.map (hom p A j c z hs hc)).hom.app (op V)))

@[expose] def frame : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
    (ActualClosedIdealModule318.object p).restrict U.ι := by
  letI := hom_isIso p A j c z hs hc
  exact asIso (hom p A j c z hs hc)

lemma frame_hom : (frame p A j c z hs hc).hom=hom p A j c z hs hc := rfl
end ActualCartierSheafFrame318
