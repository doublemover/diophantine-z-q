module
public import InfinityBasePoint318
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace InfinityWholePointStabilizer318
open Polynomial AlgebraicGeometry CategoryTheory InfinityReciprocalAction318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) {F:Type} [Field F] [Algebra ℚ F]
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
local instance pointAlgebra:Algebra (Base c) F:=(InfinityBasePoint318.fieldPoint c).toAlgebra
variable (q:Spec (CommRingCat.of F)⟶ContactProjectiveModel318.model c)
    (hq:q≫ContactProjectiveModel318.modelMap c=InfinityBasePoint318.infinityPoint (F:=F))
include hq
lemma range_infinity:Set.range q⊆Set.range (InfinityGlobalScheme318.chartEmbedding c):=by
  rintro y ⟨x,rfl⟩
  change q x∈(InfinityGlobalScheme318.chartEmbedding c).opensRange
  rw [InfinityGlobalScheme318.chartEmbedding_range]
  change ContactProjectiveModel318.modelMap c (q x)∈(InfinityGlobalBase318.baseOpen c ''ᵁ ⊤)
  have h: q≫ContactProjectiveModel318.modelMap c=
      Spec.map (CommRingCat.ofHom (InfinityBasePoint318.fieldPoint (F:=F) c))≫
        InfinityGlobalBase318.baseOpen c:=hq.trans (InfinityBasePoint318.fieldPoint_over_infinity c).symm
  have hx:=congrArg (fun f=>f x) h
  exact ⟨Spec.map (CommRingCat.ofHom (InfinityBasePoint318.fieldPoint (F:=F) c)) x,trivial,hx.symm⟩
/-- Every actual global field-valued source point above the projective
infinity point has the required original whole-chart presentation. -/
theorem exists_chart_point:∃p:Order c→+*F,
    p (InfinityPrimeSignInertia318.reciprocalCoordinate c)=0∧InfinitySignPoint318.point c p=q:=by
  let f:Spec (CommRingCat.of F)⟶ReciprocalInfinityNormalization318.neighborhood c:=IsOpenImmersion.lift (InfinityGlobalScheme318.chartEmbedding c) q (range_infinity c q hq)
  have hf:f≫InfinityGlobalScheme318.chartEmbedding c=q:=IsOpenImmersion.lift_fac _ _ _
  have hb:f≫Spec.algebraMap (Base c) (Order c)=Spec.algebraMap (Base c) F:=by
    apply (cancel_mono (InfinityGlobalBase318.baseOpen c)).mp
    have hc:InfinityGlobalScheme318.chartEmbedding c≫ContactProjectiveModel318.modelMap c=
        Spec.algebraMap (Base c) (Order c)≫InfinityGlobalBase318.baseOpen c:=
      InfinityStructureMap318.chartEmbedding_over_contact_line c
    rw [Category.assoc,←hc,←Category.assoc,hf]
    exact hq.trans (InfinityBasePoint318.fieldPoint_over_infinity c).symm
  let p:Order c→ₐ[Base c]F:=Spec.homEquivAlgHom ⟨f,hb⟩
  have hp:Spec.map (CommRingCat.ofHom p.toRingHom)=f:=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨f,hb⟩)
  refine ⟨p.toRingHom,?_,?_⟩
  · change p (algebraMap (Base c) (Order c) (algebraMap ℚ[X] (Base c) Polynomial.X))=0
    rw [p.commutes]
    exact InfinityBasePoint318.fieldPoint_coordinate c
  · unfold InfinitySignPoint318.point
    rw [hp,hf]
/-- Complete original-source point coverage, with no assumed affine
presentation: the only stabilizing original signs at infinity are the two
constant sign patterns. This is not identity on the nonreduced fiber. -/
theorem fixed_exactly (b:Fin 4→Bool):q≫ContactGlobalSigns318.map c b=q↔
    b=(fun _=>false)∨b=(fun _=>true):=by
  obtain ⟨p,hs,hp⟩:=exists_chart_point c q hq
  rw [←hp]
  exact InfinitySignPoint318.fixed_exactly c p hs b
end InfinityWholePointStabilizer318
