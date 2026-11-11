module
public import IntrinsicChartFrames318
public import OpenLineFrameCoordinates318
public section
noncomputable section
namespace ActualIntrinsicFrameUnitComparison318
section Linear
variable {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]
/-- The coefficient of a genuine module generator in ANY genuine frame
is an actual ring unit, not merely a nonzero fraction-field scalar. -/
lemma generator_coefficient_unit(e:R≃ₗ[R]M)(g:M)
    (hg:Function.Surjective (fun a:R=>a • g)):IsUnit (e.symm g):=by
  obtain ⟨a,ha⟩:=hg (e 1)
  have hc:a*e.symm g=1:=by
    have h:=congrArg e.symm ha
    simpa only [map_smul,LinearEquiv.symm_apply_apply,smul_eq_mul] using h
  exact isUnit_iff_exists_inv.mpr ⟨a,(mul_comm _ _).trans hc⟩
lemma coefficient_multiple(e:R≃ₗ[R]M)(g:M)(a:R):e.symm (a • g)=a*e.symm g:=by
  rw [map_smul,smul_eq_mul]
end Linear
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {Y:Scheme.{u}} {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j:Spec (CommRingCat.of S)⟶Y) [IsOpenImmersion j]
    (p:Y⟶Spec (CommRingCat.of R))
    (h:j≫p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (e:KaehlerDifferential R S≃ₗ[S]S)
    (ω:KaehlerDifferential R S)(hω:e ω=1)
variable (V:Y.Opens)(hV:V≤j ''ᵁ ⊤)
    (frame:Γ(Y,V)≃ₗ[Γ(Y,V)]Γ(FamilyIntrinsicDifferentials318.omega p,V))
/-- Compare the ACTUAL universal differential generator on its genuine
chart neighborhood with any produced ambient frame of the SAME sheaf.
The comparison coefficient is regular and a unit on the ENTIRE V. -/
theorem original_generator_unit:
    IsUnit (frame.symm ((FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hV).op
      (IntrinsicChartSections318.sectionMap j p h ω))):=
  generator_coefficient_unit frame _
    (IntrinsicChartFrames318.generator_bijective j p h e ω hω V hV).surjective
/-- Actual section coefficients compare through this regular unit;
there is no assumed equality of independently transported frames. -/
theorem original_multiple_coefficient(a:Γ(Y,V)):
    frame.symm (a • (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hV).op
      (IntrinsicChartSections318.sectionMap j p h ω))=
      a*frame.symm ((FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hV).op
        (IntrinsicChartSections318.sectionMap j p h ω)):=
  coefficient_multiple frame _ a
end ActualIntrinsicFrameUnitComparison318
