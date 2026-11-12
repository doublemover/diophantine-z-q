module
public import FourRootGluedScheme318
public section
noncomputable section
namespace FourRootSchemeChartInputs318
open AlgebraicGeometry CategoryTheory
open FourRootCoordinateOverlap318 FourRootGluedScheme318
variable (b:Fin 4→ℂ) {S:Type} [CommRing S] [Algebra ℂ S]
@[expose] def finiteInput (f:Affine b→ₐ[ℂ]S):Spec (CommRingCat.of S)⟶scheme b:=
  Spec.map (CommRingCat.ofHom f.toRingHom)≫finiteChart b
@[expose] def infinityInput (f:Infinity b→ₐ[ℂ]S):Spec (CommRingCat.of S)⟶scheme b:=
  Spec.map (CommRingCat.ofHom f.toRingHom)≫infinityChart b
lemma finite_base (f:Affine b→ₐ[ℂ]S):finiteInput b f≫structureMap b=Spec.algebraMap ℂ S:=by
  rw [finiteInput,Category.assoc,finite_structure]
  unfold finiteBase
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact f.commutes a
lemma infinity_base (f:Infinity b→ₐ[ℂ]S):infinityInput b f≫structureMap b=Spec.algebraMap ℂ S:=by
  rw [infinityInput,Category.assoc,infinity_structure]
  unfold infinityBase
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact f.commutes a

lemma finite_injective {f g:Affine b→ₐ[ℂ]S} (h:finiteInput b f=finiteInput b g):f=g:=by
  apply AlgHom.ext
  intro a
  exact congrArg (fun q=>q.hom a) (Spec.map_injective ((cancel_mono (finiteChart b)).mp h))
lemma infinity_injective {f g:Infinity b→ₐ[ℂ]S} (h:infinityInput b f=infinityInput b g):f=g:=by
  apply AlgHom.ext
  intro a
  exact congrArg (fun q=>q.hom a) (Spec.map_injective ((cancel_mono (infinityChart b)).mp h))

/-- Equality of actual finite/infinity Scheme inputs factors through the
ACTUAL localization intersection, rather than a pointwise intersection
invented after gluing. -/
lemma overlap_hom (f:Affine b→ₐ[ℂ]S) (g:Infinity b→ₐ[ℂ]S)
    (h:finiteInput b f=infinityInput b g):
    ∃k:InfinityOverlap b→+*S,
      (∀a,k (toInfinityBase b a)=f a) ∧
      (∀a,k (algebraMap (Infinity b) (InfinityOverlap b) a)=g a):=by
  let l:=overlapLift b (Spec.map (CommRingCat.ofHom f.toRingHom))
    (Spec.map (CommRingCat.ofHom g.toRingHom)) h
  obtain ⟨k,hk⟩:=Spec.map_surjective l
  have hf:=overlapLift_finite b (Spec.map (CommRingCat.ofHom f.toRingHom))
    (Spec.map (CommRingCat.ofHom g.toRingHom)) h
  have hg:=overlapLift_infinity b (Spec.map (CommRingCat.ofHom f.toRingHom))
    (Spec.map (CommRingCat.ofHom g.toRingHom)) h
  change l≫_=_ at hf hg
  rw [←hk,intoFinite_eq,←Spec.map_comp] at hf
  rw [←hk] at hg
  change Spec.map k≫Spec.map (CommRingCat.ofHom (algebraMap (Infinity b) (InfinityOverlap b)))=_ at hg
  rw [←Spec.map_comp] at hg
  exact ⟨k.hom,fun a=>congrArg (fun q=>q.hom a) (Spec.map_injective hf),
    fun a=>congrArg (fun q=>q.hom a) (Spec.map_injective hg)⟩

/-- The zeroth root and normalized u are actual inverse units on EVERY
common Scheme-valued input. In particular u=0 cannot belong to the finite
chart, even over algebras with nilpotents. -/
lemma transition_unit (f:Affine b→ₐ[ℂ]S) (g:Infinity b→ₐ[ℂ]S)
    (h:finiteInput b f=infinityInput b g):
    g (FourRootInfinityCoordinateRing318.coordinate b none)*
      f (FourRootAffineCoordinateRing318.coordinate b (some 0))=1:=by
  obtain ⟨k,hf,hg⟩:=overlap_hom b f g h
  have hz:=hf (FourRootAffineCoordinateRing318.coordinate b (some 0))
  simp only [toInfinityBase_z,s_zero,map_mul,map_one,one_mul] at hz
  rw [←hg,←hz,←map_mul]
  exact (congrArg k (u_ui b)).trans (map_one k)

/-- A normalized infinity input whose actual u is a unit extends to the
actual overlap, and the fixed gluing identifies it with the specified
finite-ring map. -/
@[expose] def overlapEvaluation (g:Infinity b→ₐ[ℂ]S)
    (hu:IsUnit (g (FourRootInfinityCoordinateRing318.coordinate b none))):
    InfinityOverlap b→ₐ[ℂ]S:=
  IsLocalization.Away.liftAlgHom (f:=g) (FourRootInfinityCoordinateRing318.coordinate b none) hu
@[simp] lemma overlapEvaluation_map (g:Infinity b→ₐ[ℂ]S) (hu) (a:Infinity b):
    overlapEvaluation b g hu (algebraMap (Infinity b) (InfinityOverlap b) a)=g a:=by
  simp [overlapEvaluation,IsLocalization.Away.liftAlgHom_apply]
lemma input_agreement (g:Infinity b→ₐ[ℂ]S) (hu):
    finiteInput b ((overlapEvaluation b g hu).comp (toInfinityBase b))=infinityInput b g:=by
  have hl:Spec.map (CommRingCat.ofHom (overlapEvaluation b g hu).toRingHom)≫intoInfinity b=
      Spec.map (CommRingCat.ofHom g.toRingHom):=by
    unfold intoInfinity
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact overlapEvaluation_map b g hu a
  calc
    _=Spec.map (CommRingCat.ofHom (overlapEvaluation b g hu).toRingHom)≫intoFinite b≫finiteChart b:=by
      rw [intoFinite_eq,←Spec.map_comp]
      rfl
    _=Spec.map (CommRingCat.ofHom (overlapEvaluation b g hu).toRingHom)≫intoInfinity b≫infinityChart b:=by
      rw [chart_overlap]
    _=infinityInput b g:=by rw [←Category.assoc,hl];rfl
end FourRootSchemeChartInputs318
