module
public import IntrinsicChartSectionAction318
public section
noncomputable section
namespace IntrinsicChartRepresentation318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p:X⟶Spec (CommRingCat.of R)) (j:Spec (CommRingCat.of S)⟶X) [IsOpenImmersion j]
    (hj:j≫p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
/-- The actual algebraic representative of a global intrinsic differential
on the whole specified affine chart, through the canonical section equivalence. -/
@[expose] def representation (s:Γ(FamilyIntrinsicDifferentials318.omega p,⊤)):
    KaehlerDifferential R S:=
  (IntrinsicAffineSectionEquiv318.equivalence j p hj).symm
    ((FamilyIntrinsicDifferentials318.omega p).presheaf.map
      (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op s)
theorem representation_restrict (s:Γ(FamilyIntrinsicDifferentials318.omega p,⊤)):
    IntrinsicChartSections318.sectionMap j p hj (representation p j hj s)=
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map
        (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op s:=
  (IntrinsicAffineSectionEquiv318.equivalence j p hj).apply_symm_apply _
/-- Canonical representatives intertwine the actual global pullback and
actual algebraic pullback whenever the original chart square commutes. -/
theorem representation_action (f:X⟶X) (hf:f≫p=p) (a:S→ₐ[R]S)
    (hsquare:j≫f=Spec.map (CommRingCat.ofHom a.toRingHom)≫j)
    (s:Γ(FamilyIntrinsicDifferentials318.omega p,⊤)):
    representation p j hj (IntrinsicDifferentialPullback318.globalSection f p p hf s)=
      AlgHomDifferential318.map a (representation p j hj s):=
  IntrinsicChartSectionAction318.representative_action p j hj f hf a hsquare s
    (representation p j hj s)
    (representation p j hj (IntrinsicDifferentialPullback318.globalSection f p p hf s))
    (representation_restrict p j hj s) (representation_restrict p j hj _)
end IntrinsicChartRepresentation318
