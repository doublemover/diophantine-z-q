module

public import OriginalRetainedProjectiveNormalization318

@[expose] public section
noncomputable section

namespace OriginalRetainedProjectiveAffinePiece318

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι : Type) [Fintype ι] [DecidableEq ι]

section ClosedScheme

variable {X : Scheme} (embedding : X⟶Ambient ι)

abbrev pulledPiece (i : ι) : Scheme := pullback embedding (affineArrow ι i)
abbrev pulledFirst (i : ι) : pulledPiece ι embedding i⟶X :=
  pullback.fst embedding (affineArrow ι i)
abbrev pulledSecond (i : ι) : pulledPiece ι embedding i⟶Spec (CommRingCat.of (Poly ι i)) :=
  pullback.snd embedding (affineArrow ι i)

variable (base : X⟶T)
variable (over : embedding≫projectiveBase ι=base)
variable [IsClosedImmersion embedding]

include over in
/-- Exact quotient of the literal dehomogenized polynomial chart.
This is consumed below on the named original retained complex fibre. -/
theorem pulled_piece_quotient (i : ι) :
    ∃ (I : Ideal (Poly ι i))
      (J : Spec (CommRingCat.of (Poly ι i ⧸ I))⟶X),
      IsOpenImmersion J ∧
      J≫embedding=Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))≫affineArrow ι i ∧
      J≫base=Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (algebraMap ℂ (Poly ι i)))) ∧
      Set.range J=Set.range (pulledFirst ι embedding i) := by
  let f : pulledPiece ι embedding i⟶X := pulledFirst ι embedding i
  let g : pulledPiece ι embedding i⟶Spec (CommRingCat.of (Poly ι i)) := pulledSecond ι embedding i
  have gClosed : IsClosedImmersion g :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback embedding (affineArrow ι i)) ‹IsClosedImmersion embedding›
  obtain ⟨I,e,he⟩ := IsClosedImmersion.Spec_iff.1 gClosed
  let j := e.inv≫f
  have xy : e.inv≫g=Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [he,←Category.assoc,e.inv_hom_id,Category.id_comp]
  have pulls : j≫embedding=Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))≫affineArrow ι i := by
    change (e.inv≫f)≫embedding=_
    rw [Category.assoc,show f≫embedding=g≫affineArrow ι i from pullback.condition,
      ←Category.assoc,xy]
  refine ⟨I,j,?_,pulls,?_,?_⟩
  · let : IsOpenImmersion f :=
      isOpenImmersion_stableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback embedding (affineArrow ι i)).flip (affineArrow_open ι i)
    let : IsIso e.inv := inferInstance
    let : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
    exact IsOpenImmersion.comp e.inv f
  · rw [←over,←Category.assoc,pulls,Category.assoc,affineArrow_base,←Spec.map_comp,
      ←CommRingCat.ofHom_comp]
  · change Set.range (e.inv≫f)=Set.range f
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨e.inv y,rfl⟩
    · rintro ⟨y,rfl⟩
      refine ⟨e.hom y,?_⟩
      change f (e.inv (e.hom y))=f y
      exact congrArg (fun z => f z)
        (congrArg (fun u : pulledPiece ι embedding i⟶pulledPiece ι embedding i => u y)
          e.hom_inv_id)

omit [IsClosedImmersion embedding] in
theorem complex_point_factors (r : T⟶X) :
    ∃ (i : ι) (r' : T⟶pulledPiece ι embedding i),r'≫pulledFirst ι embedding i=r := by
  let c : T := (default : PrimeSpectrum ℂ)
  have h : (r≫embedding) c ∈ (⊤ : (Ambient ι).Opens) := trivial
  rw [←ambient_affines_cover ι,TopologicalSpace.Opens.mem_iSup] at h
  obtain ⟨i,hi⟩ := h
  have img : Set.range (r≫embedding) ⊆ Set.range (affineArrow ι i) := by
    rintro _ ⟨z,rfl⟩
    have cz : z=c := Subsingleton.elim _ _
    rw [cz]
    rw [←affineArrow_range ι i] at hi
    exact hi
  let q := IsOpenImmersion.lift (affineArrow ι i) (r≫embedding) img
  have hq : r≫embedding=q≫affineArrow ι i :=
    (IsOpenImmersion.lift_fac _ _ _).symm
  exact ⟨i,pullback.lift r q hq,pullback.lift_fst r q hq⟩

end ClosedScheme

section OriginalRetained

variable {A Y E : Scheme} (a : A⟶Y) (P33 : E⟶Y) (σ : T⟶E)

def retainedCarrier : Scheme :=
  (OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33)).left
def retainedBase : retainedCarrier a P33 σ ⟶ T :=
  (OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33)).hom

variable (embedding : retainedCarrier a P33 σ⟶Ambient ι)
variable [IsClosedImmersion embedding]
variable (originalBase : embedding≫projectiveBase ι=retainedBase a P33 σ)

abbrev piece (i : ι) : Scheme := pulledPiece ι embedding i
abbrev pieceToOriginal (i : ι) : piece ι a P33 σ embedding i⟶retainedCarrier a P33 σ :=
  pulledFirst ι embedding i
abbrev pieceToAffine (i : ι) : piece ι a P33 σ embedding i⟶Spec (CommRingCat.of (Poly ι i)) :=
  pulledSecond ι embedding i

include originalBase in
/-- The actual R119/R121 retained fibre, exact closed embedding and
actual base map are specialized here, not a detached projective shell. -/
theorem actual_piece_coordinate_ring (i : ι) :
    ∃ (I : Ideal (Poly ι i))
      (J : Spec (CommRingCat.of (Poly ι i ⧸ I))⟶retainedCarrier a P33 σ),
      IsOpenImmersion J ∧
      J≫embedding=Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))≫affineArrow ι i ∧
      J≫retainedBase a P33 σ=Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (algebraMap ℂ (Poly ι i)))) ∧
      Set.range J=Set.range (pieceToOriginal ι a P33 σ embedding i) :=
  pulled_piece_quotient ι embedding (retainedBase a P33 σ) originalBase i

omit [IsClosedImmersion embedding] in
/-- This is the whole actual Spec(ℂ) arrow of the retained 33-fibre,
not a differential or a numerical coordinate tuple only. -/
theorem actual_point_factors_piece (r : T⟶retainedCarrier a P33 σ) :
    ∃ (i : ι) (r' : T⟶piece ι a P33 σ embedding i),
      r'≫pieceToOriginal ι a P33 σ embedding i=r :=
  complex_point_factors ι embedding r

end OriginalRetained
end OriginalRetainedProjectiveAffinePiece318
