module
public import FourRootCoordinateOverlap318
public import GenericOpenPushout318
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace FourRootGluedScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FourRootCoordinateOverlap318
variable (b:Fin 4→ℂ)
abbrev finiteScheme:Scheme:=Spec (CommRingCat.of (Affine b))
abbrev infinityScheme:Scheme:=Spec (CommRingCat.of (Infinity b))
abbrev overlapScheme:Scheme:=Spec (CommRingCat.of (InfinityOverlap b))
@[expose] def intoInfinity:overlapScheme b⟶infinityScheme b:=
  Spec.map (CommRingCat.ofHom (algebraMap (Infinity b) (InfinityOverlap b)))
instance intoInfinity_open:IsOpenImmersion (intoInfinity b):=
  IsOpenImmersion.of_isLocalization (FourRootInfinityCoordinateRing318.coordinate b none)
@[expose] def intoFinite:overlapScheme b⟶finiteScheme b:=
  Spec.map (overlapEquiv b).toRingEquiv.toCommRingCatIso.inv ≫
    Spec.map (CommRingCat.ofHom (algebraMap (Affine b) (AffineOverlap b)))
instance intoFinite_open:IsOpenImmersion (intoFinite b):=by
  haveI:IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Affine b) (AffineOverlap b)))):=
    IsOpenImmersion.of_isLocalization (FourRootAffineCoordinateRing318.coordinate b (some 0))
  unfold intoFinite
  infer_instance
lemma intoFinite_eq:intoFinite b=Spec.map (CommRingCat.ofHom (toInfinityBase b).toRingHom):=by
  unfold intoFinite
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact toInfinity_map b a

@[expose] def finiteBase:finiteScheme b⟶Spec (CommRingCat.of ℂ):=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (Affine b)))
@[expose] def infinityBase:infinityScheme b⟶Spec (CommRingCat.of ℂ):=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (Infinity b)))
lemma overlap_over_base:intoFinite b≫finiteBase b=intoInfinity b≫infinityBase b:=by
  rw [intoFinite_eq]
  unfold finiteBase intoInfinity infinityBase
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (toInfinityBase b).commutes a

/-- Actual Scheme pushout along the two specified PRINCIPAL OPEN
immersions, not a scheme structure transported from complex points. -/
abbrev scheme:Scheme:=pushout (intoFinite b) (intoInfinity b)
@[expose] def finiteChart:finiteScheme b⟶scheme b:=pushout.inl _ _
@[expose] def infinityChart:infinityScheme b⟶scheme b:=pushout.inr _ _
instance finiteChart_open:IsOpenImmersion (finiteChart b):=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoFinite b) (intoInfinity b)) WalkingSpan.left))
instance infinityChart_open:IsOpenImmersion (infinityChart b):=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoFinite b) (intoInfinity b)) WalkingSpan.right))
@[reassoc] lemma chart_overlap:intoFinite b≫finiteChart b=intoInfinity b≫infinityChart b:=
  pushout.condition
/-- The actual scheme intersection is exactly the literal principal
localization, including all residue and nilpotent structure. -/
theorem chart_square:IsPullback (intoFinite b) (intoInfinity b) (finiteChart b) (infinityChart b):=
  GenericOpenPushout318.square (intoFinite b) (intoInfinity b)
@[expose] def overlapLift {X:Scheme} (f:X⟶finiteScheme b) (g:X⟶infinityScheme b)
    (h:f≫finiteChart b=g≫infinityChart b):X⟶overlapScheme b:=
  (chart_square b).lift f g h
@[reassoc] lemma overlapLift_finite {X:Scheme} (f:X⟶finiteScheme b) (g:X⟶infinityScheme b)
    (h:f≫finiteChart b=g≫infinityChart b):overlapLift b f g h≫intoFinite b=f:=
  (chart_square b).lift_fst f g h
@[reassoc] lemma overlapLift_infinity {X:Scheme} (f:X⟶finiteScheme b) (g:X⟶infinityScheme b)
    (h:f≫finiteChart b=g≫infinityChart b):overlapLift b f g h≫intoInfinity b=g:=
  (chart_square b).lift_snd f g h

@[expose] def structureMap:scheme b⟶Spec (CommRingCat.of ℂ):=
  pushout.desc (finiteBase b) (infinityBase b) (overlap_over_base b)
@[reassoc,simp] lemma finite_structure:finiteChart b≫structureMap b=finiteBase b:=pushout.inl_desc ..
@[reassoc,simp] lemma infinity_structure:infinityChart b≫structureMap b=infinityBase b:=pushout.inr_desc ..

/-- Every SCHEME point, not only every listed complex tuple, lies on one
of the genuine two affine charts. -/
theorem charts_cover (p:scheme b):
    (∃a,finiteChart b a=p) ∨ (∃c,infinityChart b c=p):=by
  obtain ⟨i,q,hq⟩:=Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoFinite b) (intoInfinity b)) p
  cases i with
  | none=>
    left
    refine ⟨intoFinite b q,?_⟩
    change (intoFinite b≫finiteChart b) q=p
    rw [show intoFinite b≫finiteChart b=
      colimit.ι (span (intoFinite b) (intoInfinity b)) WalkingSpan.zero from
        colimit.w (span (intoFinite b) (intoInfinity b)) WalkingSpan.Hom.fst]
    exact hq
  | some j=>
    cases j with
    | left=>exact Or.inl ⟨q,hq⟩
    | right=>exact Or.inr ⟨q,hq⟩

@[ext] theorem hom_ext {X:Scheme} {f g:scheme b⟶X}
    (hf:finiteChart b≫f=finiteChart b≫g)
    (hi:infinityChart b≫f=infinityChart b≫g):f=g:=
  pushout.hom_ext hf hi
end FourRootGluedScheme318
