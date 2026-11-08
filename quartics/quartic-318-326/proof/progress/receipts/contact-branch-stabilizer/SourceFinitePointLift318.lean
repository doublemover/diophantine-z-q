module
public import SourceBranchPointAction318
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace SourceFinitePointLift318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) {F:Type} [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
variable (q:Spec (CommRingCat.of F)⟶ContactProjectiveModel318.model c)
    (h:q≫ContactProjectiveModel318.modelMap c=
      Spec.algebraMap R F≫JLineAtlas318.chart ℚ 1)
include h
lemma range_finite:Set.range q⊆Set.range (SourceGlobalAffine318.chartEmbedding c):=by
  rintro y ⟨x,rfl⟩
  change q x∈(SourceGlobalAffine318.chartEmbedding c).opensRange
  rw [SourceGlobalAffine318.chartEmbedding_range]
  change ContactProjectiveModel318.modelMap c (q x)∈(JLineAtlas318.chart ℚ 1 ''ᵁ ⊤)
  have hx:=congrArg (fun f=>f x) h
  change ContactProjectiveModel318.modelMap c (q x)=
    JLineAtlas318.chart ℚ 1 (Spec.algebraMap R F x) at hx
  exact ⟨Spec.algebraMap R F x,trivial,hx.symm⟩
/-- Every actual global field-valued point over the finite t-line is
represented by the actual full source order, with the same base algebra. -/
theorem exists_source_point:∃p:SourceOrder c→ₐ[R]F,SourceBranchPointAction318.point c p=q:=by
  let f:=IsOpenImmersion.lift (SourceGlobalAffine318.chartEmbedding c) q (range_finite c q h)
  have hf:f≫SourceGlobalAffine318.chartEmbedding c=q:=IsOpenImmersion.lift_fac _ _ _
  have hb:f≫Spec.algebraMap R (SourceOrder c)=Spec.algebraMap R F:=by
    apply (cancel_mono (JLineAtlas318.chart ℚ 1)).mp
    have hc:SourceGlobalAffine318.chartEmbedding c≫ContactProjectiveModel318.modelMap c=
        Spec.algebraMap R (SourceOrder c)≫JLineAtlas318.chart ℚ 1:=
      SourceGlobalAffine318.chartEmbedding_over_contact_line c
    rw [Category.assoc,←hc,←Category.assoc,hf]
    exact h
  let p:SourceOrder c→ₐ[R]F:=Spec.homEquivAlgHom ⟨f,hb⟩
  have hp:Spec.map (CommRingCat.ofHom p.toRingHom)=f:=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨f,hb⟩)
  refine ⟨p,?_⟩
  unfold SourceBranchPointAction318.point
  rw [hp,hf]
variable (i:Fin 4) (ht:algebraMap R F Polynomial.X=
  algebraMap ℚ F (LinearContactSquareclass318.contacts i))
include ht
/-- Complete actual-point coverage: no chosen finite-chart presentation is
an extra hypothesis of this branchpoint stabilizer theorem. -/
theorem stabilizer_exactly (b:Fin 4→Bool):q≫ContactGlobalSigns318.map c b=q↔
    b=(fun _=>false)∨b=SourceCharacterFields318.flip i:=by
  obtain ⟨p,hp⟩:=exists_source_point c q h
  rw [←hp]
  exact SourceBranchPointAction318.fixed_exactly c p i ht b
theorem stabilizer_image_card:Nat.card (Set.range
    (fun b:{b:Fin 4→Bool // q≫ContactGlobalSigns318.map c b=q}=>ContactGlobalSigns318.map c b.val))=2:=by
  obtain ⟨p,hp⟩:=exists_source_point c q h
  rw [←hp]
  exact SourceBranchPointAction318.stabilizer_image_card c p i ht
end SourceFinitePointLift318
