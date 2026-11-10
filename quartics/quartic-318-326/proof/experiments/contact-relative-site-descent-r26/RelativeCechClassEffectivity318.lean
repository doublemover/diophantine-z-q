module
public import RigidifiedCechDatum318
public section
noncomputable section
namespace RelativeCechClassEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318 RelativeRigidifiedLine318
open RigidifiedRelativeClass318 RelativeLineClassQuotient318
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318 RigidifiedCechNerve318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (pointed : e' ≫ f = g ≫ e)
  (p : X ⟶ S) (p' : X' ⟶ S') (square : f ≫ p = p' ≫ g)
  (hs' : e' ≫ p' = 𝟙 S')

abbrev doubleProjection := doubleMap g f p' p square.symm

@[expose] def firstMap : RelativeClass p' →* RelativeClass (doubleProjection f g p p' square) :=
  RelativeLineClassQuotient318.map p' (doubleProjection f g p p' square)
    (first f) (first g) (double_first g f p' p square.symm).symm
@[expose] def secondMap : RelativeClass p' →* RelativeClass (doubleProjection f g p p' square) :=
  RelativeLineClassQuotient318.map p' (doubleProjection f g p p' square)
    (second f) (second g) (double_second g f p' p square.symm).symm

variable (c : RelativeClass p')
  (matching : firstMap f g p p' square c = secondMap f g p p' square c)
  (hd : Function.Bijective (doubleSection f g e e' pointed).appTop)

abbrev localRepresentative := RigidifiedClassQuotient318.representative e' p' hs' c

/-- The supplied equality is an equality of the two original relative
pullback classes. It selects a unique compatible isomorphism of the actual
original double pullbacks, not a freely chosen cocycle. -/
@[expose] def overlap : Overlap f g e e' pointed (localRepresentative e' p' hs' c) :=
  RigidifiedIsoCoherence318.transition (doubleSection f g e e' pointed)
    (doubleProjection f g p p' square)
    (double_section f g e e' pointed p p' hs' square.symm) hd (by
      change relativeClass (doubleProjection f g p p' square) (doubleSection f g e e' pointed)
          (RigidifiedPointedPullback318.line e' (doubleSection f g e e' pointed)
            (first f) (first g) (double_first f g e' e pointed) (localRepresentative e' p' hs' c)) =
        relativeClass (doubleProjection f g p p' square) (doubleSection f g e e' pointed)
          (RigidifiedPointedPullback318.line e' (doubleSection f g e e' pointed)
            (second f) (second g) (double_second f g e' e pointed) (localRepresentative e' p' hs' c))
      rw [RigidifiedPointedPullback318.relativeClass_line e' _ _ _ _ p' _
          (double_first g f p' p square.symm).symm,
        RigidifiedPointedPullback318.relativeClass_line e' _ _ _ _ p' _
          (double_second g f p' p square.symm).symm,
        RigidifiedClassQuotient318.representative_class]
      exact matching)

variable (hl : Function.Injective e'.appTop)
  (ht : Function.Injective (tripleSection f g e e' pointed).appTop)

@[expose] def datum : OriginalSchemeDescentData318.Datum f :=
  RigidifiedCechDatum318.datum f g e e' pointed (localRepresentative e' p' hs' c)
    (overlap f g e e' pointed p p' square hs' c matching hd) hl ht

variable [IsAffineHom f] [Flat f] [Surjective f]

/-- A matching original relative class is effective under the displayed
actual nerve rigidity hypotheses. The witness is the original reconstructed
line; no representation, global trivialization or cocycle law is assumed. -/
@[expose] def descendedClass : RelativeClass p :=
  classMap p (classOf (AffineMorphismGlobalEffectivity318.line f
    (datum f g e e' pointed p p' square hs' c matching hd hl ht)))

lemma descendedClass_pullback :
    RelativeLineClassQuotient318.map p p' f g square
      (descendedClass f g e e' pointed p p' square hs' c matching hd hl ht) = c := by
  have h := LineSheafClass318.classOf_eq
    (AffineMorphismGlobalEffectivity318.comparison f
      (datum f g e e' pointed p p' square hs' c matching hd hl ht))
  have hr := congrArg (classMap p') h
  change RelativeLineClassQuotient318.map p p' f g square
      (descendedClass f g e e' pointed p p' square hs' c matching hd hl ht) =
    relativeClass p' e' (localRepresentative e' p' hs' c) at hr
  exact hr.trans (RigidifiedClassQuotient318.representative_class e' p' hs' c)

include hs' matching hd hl ht in
/-- Existence for the original relative-class Čech equalizer, with an
actual descended original line as its witness. -/
theorem matching_effective : ∃ d : RelativeClass p,
    RelativeLineClassQuotient318.map p p' f g square d = c :=
  ⟨descendedClass f g e e' pointed p p' square hs' c matching hd hl ht,
    descendedClass_pullback f g e e' pointed p p' square hs' c matching hd hl ht⟩
end RelativeCechClassEffectivity318
