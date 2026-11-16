module
public import WeierstrassReciprocalOverlap318
public import Mathlib.AlgebraicGeometry.Gluing
import all WeierstrassGluing318
public section
noncomputable section
namespace WeierstrassXProjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open WeierstrassReciprocalCoordinate318 WeierstrassReciprocalOverlap318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type*} [CommRing R] (A B:R)

lemma chart_ranges_cover:
    (WeierstrassGluing318.intoInfinity A B).opensRange⊔(nearBase A B).opensRange=⊤:=by
  have h1:(WeierstrassGluing318.intoInfinity A B).opensRange=
      PrimeSpectrum.basicOpen (InfinityChart318.z A B):=by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range _ _
  have h2:(nearBase A B).opensRange=PrimeSpectrum.basicOpen (denominator A B):=by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range _ _
  rw [h1,h2]
  exact basicOpen_cover A B

@[expose] def chart:Bool→Scheme
  | false=>WeierstrassGluing318.overlap A B
  | true=>Spec (CommRingCat.of (Near A B))
@[expose] def embedding:(b:Bool)→chart A B b⟶InfinitySmooth318.scheme A B
  | false=>WeierstrassGluing318.intoInfinity A B
  | true=>nearBase A B
instance embedding_open (b:Bool):IsOpenImmersion (embedding A B b):=by
  cases b <;> dsimp [embedding] <;> infer_instance
@[expose] def cover:(InfinitySmooth318.scheme A B).OpenCover where
  I₀:=Bool
  X:=chart A B
  f:=embedding A B
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro p
    have hp:p∈(WeierstrassGluing318.intoInfinity A B).opensRange⊔(nearBase A B).opensRange:=by
      rw [chart_ranges_cover]
      trivial
    rcases hp with hp|hp
    · obtain ⟨q,hq⟩:=hp
      exact ⟨false,q,hq⟩
    · obtain ⟨q,hq⟩:=hp
      exact ⟨true,q,hq⟩

lemma compatibility_of_actual_pullback {P X Y Z T:Scheme}
    {a:P⟶X} {b:P⟶Y} {f:X⟶Z} {g:Y⟶Z} (h:IsPullback a b f g)
    (F:X⟶T) (G:Y⟶T) (hab:a≫F=b≫G):
    pullback.fst f g≫F=pullback.snd f g≫G:=by
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [←Category.assoc,h.isoPullback_hom_fst,h.isoPullback_hom_snd] using hab
lemma diagonal_compatibility {X Z T:Scheme} (f:X⟶Z) [Mono f] (F:X⟶T):
    pullback.fst f f≫F=pullback.snd f f≫F:=by
  have h:pullback.fst f f=pullback.snd f f:=(cancel_mono f).mp pullback.condition
  rw [h]
@[expose] def localProjection:(b:Bool)→(cover A B).X b⟶ProjectiveJLine318.scheme R
  | false=>overlapProjection A B
  | true=>nearProjection A B
lemma compatible (b d:Bool):
    pullback.fst ((cover A B).f b) ((cover A B).f d)≫localProjection A B b=
    pullback.snd _ _≫localProjection A B d:=by
  cases b <;> cases d
  · exact diagonal_compatibility _ _
  · exact compatibility_of_actual_pullback (actual_pullback A B)
      _ _ (projection_compatibility A B)
  · exact compatibility_of_actual_pullback (actual_pullback A B).flip
      _ _ (projection_compatibility A B).symm
  · exact diagonal_compatibility _ _
@[expose] def infinityProjection:InfinitySmooth318.scheme A B⟶ProjectiveJLine318.scheme R:=
  (cover A B).glueMorphisms (localProjection A B) (compatible A B)
lemma infinityProjection_overlap:
    WeierstrassGluing318.intoInfinity A B≫infinityProjection A B=overlapProjection A B:=
  (cover A B).ι_glueMorphisms (localProjection A B) (compatible A B) false
lemma infinityProjection_near:
    nearBase A B≫infinityProjection A B=nearProjection A B:=
  (cover A B).ι_glueMorphisms (localProjection A B) (compatible A B) true

@[expose] def finiteProjection:ShortAffineScheme318.scheme A B⟶ProjectiveJLine318.scheme R:=
  Spec.map (CommRingCat.ofHom
    (Polynomial.aeval (R:=R) (ShortAffineJacobian318.x A B)).toRingHom)≫JLineAtlas318.chart R 1
lemma finiteProjection_overlap:
    WeierstrassGluing318.intoAffine A B≫finiteProjection A B=overlapProjection A B:=by
  rw [WeierstrassGluing318.intoAffine_eq]
  unfold finiteProjection overlapProjection
  rw [←Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,
      WeierstrassOverlap318.toInfinityBase_x]

/-- The actual x-coordinate morphism on the entire completed cubic. -/
@[expose] def xMap:WeierstrassGluing318.scheme A B⟶ProjectiveJLine318.scheme R:=
  pushout.desc (finiteProjection A B) (infinityProjection A B)
    ((finiteProjection_overlap A B).trans (infinityProjection_overlap A B).symm)
lemma finiteChart_xMap:
    WeierstrassGluing318.finiteChart A B≫xMap A B=finiteProjection A B:=pushout.inl_desc ..
lemma infinityChart_xMap:
    WeierstrassGluing318.infinityChart A B≫xMap A B=infinityProjection A B:=pushout.inr_desc ..
end WeierstrassXProjection318
