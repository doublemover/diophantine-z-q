module
public import InfinitySignChart318
public section
noncomputable section
namespace InfinitySignPoint318
open AlgebraicGeometry CategoryTheory InfinityReciprocalAction318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) {F:Type} [Field F] [Algebra ℚ F] (p:Order c→+*F)
@[expose] def point:Spec (CommRingCat.of F)⟶ContactProjectiveModel318.model c:=
  Spec.map (CommRingCat.ofHom p)≫InfinityGlobalScheme318.chartEmbedding c
/-- Exact stabilizer of the actual global source point over the original
reciprocal s=0, retaining the specified whole-chart and global sign maps. -/
theorem fixed_exactly (hs:p (InfinityPrimeSignInertia318.reciprocalCoordinate c)=0)
    (b:Fin 4→Bool):point c p≫ContactGlobalSigns318.map c b=point c p↔
      b=(fun _=>false)∨b=(fun _=>true):=by
  rw [←InfinityPrimeSignInertia318.residue_fixed_exactly c p hs b]
  constructor
  · intro h
    have hh:(Spec.map (CommRingCat.ofHom p)≫InfinitySignChart318.map c b)≫
        InfinityGlobalScheme318.chartEmbedding c=
      Spec.map (CommRingCat.ofHom p)≫InfinityGlobalScheme318.chartEmbedding c:=by
      simpa only [Category.assoc,InfinitySignChart318.actual_square,point] using h
    have ha:Spec.map (CommRingCat.ofHom p)≫InfinitySignChart318.map c b=
        Spec.map (CommRingCat.ofHom p):=
      (cancel_mono (InfinityGlobalScheme318.chartEmbedding c)).mp hh
    unfold InfinitySignChart318.map at ha
    rw [←Spec.map_comp] at ha
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ha)
  · intro h
    have ha:Spec.map (CommRingCat.ofHom p)≫InfinitySignChart318.map c b=
        Spec.map (CommRingCat.ofHom p):=by
      unfold InfinitySignChart318.map
      rw [←Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext h
    unfold point
    rw [Category.assoc,←InfinitySignChart318.actual_square,←Category.assoc,ha]
end InfinitySignPoint318
