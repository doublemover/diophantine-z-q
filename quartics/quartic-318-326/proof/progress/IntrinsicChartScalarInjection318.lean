module
public import IntrinsicAffineSectionEquiv318
public import ScaledGlobalSectionRestriction318
public section
noncomputable section
namespace IntrinsicChartScalarInjection318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j:Spec (CommRingCat.of S)⟶X) [IsOpenImmersion j]
    (p:X⟶Spec (CommRingCat.of R))
    (h:j≫p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
lemma scalar_bijective:Function.Bijective (ScaledGlobalSectionRestriction318.scalar j):=
  (ConcreteCategory.bijective_of_isIso (j.appIso ⊤).inv).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)
/-- Multiplication by an actual chart differential with unit frame value
is injective on actual ambient regular functions on the whole chart. -/
theorem injective (e:KaehlerDifferential R S≃ₗ[S]S) (ω:KaehlerDifferential R S)
    (hw:IsUnit (e ω)):
    Function.Injective (fun a:Γ(X,j ''ᵁ ⊤)=>a • IntrinsicChartSections318.sectionMap j p h ω):=by
  intro a b hab
  obtain ⟨a',rfl⟩:=(scalar_bijective j).surjective a
  obtain ⟨b',rfl⟩:=(scalar_bijective j).surjective b
  apply congrArg (ScaledGlobalSectionRestriction318.scalar j)
  have he:a' • ω=b' • ω:=by
    apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p h).injective
    simpa only [IntrinsicChartSections318.section_smul,ScaledGlobalSectionRestriction318.scalar] using hab
  have hf:=congrArg e he
  simp only [map_smul,smul_eq_mul] at hf
  exact hw.mul_left_inj.mp hf
end IntrinsicChartScalarInjection318
