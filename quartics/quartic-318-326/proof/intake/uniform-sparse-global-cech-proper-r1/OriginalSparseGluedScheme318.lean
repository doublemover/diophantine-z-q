module
public import OriginalSparseQuadraticCharts318
public import GenericOpenPushout318
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace OriginalSparseGluedScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalSparseQuadraticCharts318
universe u
variable {R : Type u} [CommRing R] (s t : R)
abbrev finiteScheme : Scheme := Spec (CommRingCat.of (CF s t))
abbrev infinityScheme : Scheme := Spec (CommRingCat.of (CG s t))
abbrev overlapScheme : Scheme := Spec (CommRingCat.of (LG s t))

@[expose] def intoInfinity : overlapScheme s t ⟶ infinityScheme s t :=
  Spec.map (CommRingCat.ofHom (algebraMap (CG s t) (LG s t)))
instance intoInfinity_open : IsOpenImmersion (intoInfinity s t) :=
  IsOpenImmersion.of_isLocalization (x (G s t))

@[expose] def intoFinite : overlapScheme s t ⟶ finiteScheme s t :=
  Spec.map (overlapEquiv s t).toRingEquiv.toCommRingCatIso.inv ≫
    Spec.map (CommRingCat.ofHom (algebraMap (CF s t) (LF s t)))
instance intoFinite_open : IsOpenImmersion (intoFinite s t) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (CF s t) (LF s t)))) :=
    IsOpenImmersion.of_isLocalization (x (F s t))
  unfold intoFinite
  infer_instance

lemma intoFinite_eq : intoFinite s t =
    Spec.map (CommRingCat.ofHom (finToInfBase s t).toRingHom) := by
  unfold intoFinite
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact finToInf_map s t a

@[expose] def finiteBase:finiteScheme s t⟶Spec (CommRingCat.of R):=
  Spec.map (CommRingCat.ofHom (algebraMap R (CF s t)))
@[expose] def infinityBase:infinityScheme s t⟶Spec (CommRingCat.of R):=
  Spec.map (CommRingCat.ofHom (algebraMap R (CG s t)))
lemma overlap_over_base:intoFinite s t≫finiteBase s t=intoInfinity s t≫infinityBase s t:=by
  rw [intoFinite_eq]
  unfold finiteBase intoInfinity infinityBase
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (finToInfBase s t).commutes a

/-- Actual Scheme pushout along the two specified PRINCIPAL OPEN
immersions, not a scheme structure transported from complex points. -/
abbrev scheme:Scheme:=pushout (intoFinite s t) (intoInfinity s t)
@[expose] def finiteChart:finiteScheme s t⟶scheme s t:=pushout.inl _ _
@[expose] def infinityChart:infinityScheme s t⟶scheme s t:=pushout.inr _ _
instance finiteChart_open:IsOpenImmersion (finiteChart s t):=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoFinite s t) (intoInfinity s t)) WalkingSpan.left))
instance infinityChart_open:IsOpenImmersion (infinityChart s t):=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoFinite s t) (intoInfinity s t)) WalkingSpan.right))
@[reassoc] lemma chart_overlap:intoFinite s t≫finiteChart s t=intoInfinity s t≫infinityChart s t:=
  pushout.condition
/-- The actual scheme intersection is exactly the literal principal
localization, including all residue and nilpotent structure. -/
theorem chart_square:IsPullback (intoFinite s t) (intoInfinity s t) (finiteChart s t) (infinityChart s t):=
  GenericOpenPushout318.square (intoFinite s t) (intoInfinity s t)
@[expose] def overlapLift {X:Scheme} (f:X⟶finiteScheme s t) (g:X⟶infinityScheme s t)
    (h:f≫finiteChart s t=g≫infinityChart s t):X⟶overlapScheme s t:=
  (chart_square s t).lift f g h
@[reassoc] lemma overlapLift_finite {X:Scheme} (f:X⟶finiteScheme s t) (g:X⟶infinityScheme s t)
    (h:f≫finiteChart s t=g≫infinityChart s t):overlapLift s t f g h≫intoFinite s t=f:=
  (chart_square s t).lift_fst f g h
@[reassoc] lemma overlapLift_infinity {X:Scheme} (f:X⟶finiteScheme s t) (g:X⟶infinityScheme s t)
    (h:f≫finiteChart s t=g≫infinityChart s t):overlapLift s t f g h≫intoInfinity s t=g:=
  (chart_square s t).lift_snd f g h

@[expose] def structureMap:scheme s t⟶Spec (CommRingCat.of R):=
  pushout.desc (finiteBase s t) (infinityBase s t) (overlap_over_base s t)
@[reassoc,simp] lemma finite_structure:finiteChart s t≫structureMap s t=finiteBase s t:=pushout.inl_desc ..
@[reassoc,simp] lemma infinity_structure:infinityChart s t≫structureMap s t=infinityBase s t:=pushout.inr_desc ..

/-- Every SCHEME point, not only every listed complex tuple, lies on one
of the genuine two affine charts. -/
theorem charts_cover (p:scheme s t):
    (∃a,finiteChart s t a=p) ∨ (∃c,infinityChart s t c=p):=by
  obtain ⟨i,q,hq⟩:=Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoFinite s t) (intoInfinity s t)) p
  cases i with
  | none=>
    left
    refine ⟨intoFinite s t q,?_⟩
    change (intoFinite s t≫finiteChart s t) q=p
    rw [show intoFinite s t≫finiteChart s t=
      colimit.ι (span (intoFinite s t) (intoInfinity s t)) WalkingSpan.zero from
        colimit.w (span (intoFinite s t) (intoInfinity s t)) WalkingSpan.Hom.fst]
    exact hq
  | some j=>
    cases j with
    | left=>exact Or.inl ⟨q,hq⟩
    | right=>exact Or.inr ⟨q,hq⟩

@[ext] theorem hom_ext {X:Scheme} {f g:scheme s t⟶X}
    (hf:finiteChart s t≫f=finiteChart s t≫g)
    (hi:infinityChart s t≫f=infinityChart s t≫g):f=g:=
  pushout.hom_ext hf hi
end OriginalSparseGluedScheme318
