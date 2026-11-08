module
public import IntrinsicChartRepresentation318
public section
noncomputable section
namespace IntrinsicChartLocalMultiple318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p:X⟶Spec (CommRingCat.of R)) (j:Spec (CommRingCat.of S)⟶X) [IsOpenImmersion j]
    (hj:j≫p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
/-- A regular multiple of the canonical algebraic representative gives an
actual whole-chart multiple of the original intrinsic global sections. -/
theorem section_multiple (s t:Γ(FamilyIntrinsicDifferentials318.omega p,⊤))
    (w:KaehlerDifferential R S)
    (ht:IntrinsicChartSections318.sectionMap j p hj w=
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map
        (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op t)
    (h:∃a:S,IntrinsicChartRepresentation318.representation p j hj s=a • w):
    ∃a:Γ(X,j ''ᵁ ⊤),
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map
        (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op s=
      a • (FamilyIntrinsicDifferentials318.omega p).presheaf.map
        (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op t:=by
  obtain ⟨a,ha⟩:=h
  refine ⟨(j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a),?_⟩
  calc
    _=IntrinsicChartSections318.sectionMap j p hj
        (IntrinsicChartRepresentation318.representation p j hj s):=
      (IntrinsicChartRepresentation318.representation_restrict p j hj s).symm
    _=IntrinsicChartSections318.sectionMap j p hj (a • w):=
      congrArg (IntrinsicChartSections318.sectionMap j p hj) ha
    _=((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a)) •
        IntrinsicChartSections318.sectionMap j p hj w:=
      IntrinsicChartSections318.section_smul j p hj a w
    _=_:=congrArg (fun v=>((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a)) • v) ht
end IntrinsicChartLocalMultiple318
