module
public import IntrinsicDifferentialSectionPullback318
public import IntrinsicAffineSectionEquiv318
public section
noncomputable section
namespace IntrinsicChartSectionAction318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p:X⟶Spec (CommRingCat.of R)) (j:Spec (CommRingCat.of S)⟶X) [IsOpenImmersion j]
    (hj:j≫p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (f:X⟶X) (hf:f≫p=p) (a:S→ₐ[R]S)
    (hsquare:j≫f=Spec.map (CommRingCat.ofHom a.toRingHom)≫j)
include hsquare in
/-- Actual whole-chart restriction commutes with a specified global
self-map and its specified affine algebra map. All objects stay abstract. -/
theorem section_action (s:Γ(FamilyIntrinsicDifferentials318.omega p,⊤))
    (ω:KaehlerDifferential R S)
    (hω:IntrinsicChartSections318.sectionMap j p hj ω=
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map
        (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op s):
    IntrinsicChartSections318.sectionMap j p hj (AlgHomDifferential318.map a ω)=
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map
        (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op
        (IntrinsicDifferentialPullback318.globalSection f p p hf s):=by
  have hv:=AffineChartPullbackScalars318.image_le f j j _ hsquare
  have hn:=DFunLike.congr_fun
    (IntrinsicDifferentialSectionPullback318.sectionMap_naturality f p p hf a j j
      hj hj hsquare hv) ω
  simp only [AddMonoidHom.comp_apply] at hn
  rw [hω] at hn
  exact hn.symm.trans (IntrinsicDifferentialSectionPullback318.globalSection_restrict
    f p p hf (j ''ᵁ ⊤) (j ''ᵁ ⊤) hv s)
include hsquare in
/-- Equality of the actual algebraic representatives, deduced using the
canonical whole-affine section equivalence rather than a field comparison. -/
theorem representative_action (s:Γ(FamilyIntrinsicDifferentials318.omega p,⊤))
    (ω ω':KaehlerDifferential R S)
    (hω:IntrinsicChartSections318.sectionMap j p hj ω=
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map
        (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op s)
    (hω':IntrinsicChartSections318.sectionMap j p hj ω'=
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map
        (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op
        (IntrinsicDifferentialPullback318.globalSection f p p hf s)):
    ω'=AlgHomDifferential318.map a ω:=by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p hj).injective
  exact hω'.trans (section_action p j hj f hf a hsquare s ω hω).symm
end IntrinsicChartSectionAction318
