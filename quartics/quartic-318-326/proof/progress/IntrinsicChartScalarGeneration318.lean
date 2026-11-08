module
public import IntrinsicChartScalarInjection318
public section
noncomputable section
namespace IntrinsicChartScalarGeneration318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j:Spec (CommRingCat.of S)⟶X) [IsOpenImmersion j]
    (p:X⟶Spec (CommRingCat.of R))
    (h:j≫p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
lemma form_multiple {V:Type*} [AddCommGroup V] [Module S V]
    (e:V≃ₗ[S]S) (ω:V) (hw:IsUnit (e ω)) (v:V):∃a:S,v=a • ω:=by
  obtain ⟨w,hw⟩:=hw
  refine ⟨e v*(↑w⁻¹:S),e.injective ?_⟩
  rw [map_smul,smul_eq_mul,←hw,mul_assoc,Units.inv_mul, mul_one]
/-- A unit value in the genuine affine differential frame gives generation
of all actual sections on the entire ambient chart. -/
theorem surjective (e:KaehlerDifferential R S≃ₗ[S]S) (ω:KaehlerDifferential R S)
    (hw:IsUnit (e ω)):
    Function.Surjective (fun a:Γ(X,j ''ᵁ ⊤)=>a • IntrinsicChartSections318.sectionMap j p h ω):=by
  intro s
  obtain ⟨v,rfl⟩:=(IntrinsicAffineSectionEquiv318.sectionMap_bijective j p h).surjective s
  obtain ⟨a,ha⟩:=form_multiple e ω hw v
  refine ⟨ScaledGlobalSectionRestriction318.scalar j a,?_⟩
  rw [ha,IntrinsicChartSections318.section_smul]
  rfl
end IntrinsicChartScalarGeneration318
