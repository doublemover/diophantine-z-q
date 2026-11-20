module
public import OriginalRCMilneFiniteGaloisLayer318
public import OriginalRCMilneActualTwistedKummer318
import all OriginalRCMilneTwistedKummerPointAction318
import all Mathlib.FieldTheory.AbsoluteGaloisGroup

public section
noncomputable section

namespace OriginalRCMilneActualKummerContinuity318

open ActualTwoDescentEllipticModel318 OriginalRCMilneFiniteGaloisLayer318
open OriginalRCMilneTwistedKummerCore318 OriginalRCMilneTwistedKummerPointAction318
open OriginalRCMilneActualTwistedKummer318

variable {F : Type*} [Field F] [CharZero F]
local notation "Fb" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Fb := Classical.decEq _
local notation "P" d => Point (algebraMap F Fb d)

def coordinates {r : Fb} : Point r → Finset Fb
  | .zero => ∅
  | .some x y _ => {x,y}

/-- The one literal coordinate layer retains both halves, their
ordered lift pairs, all input points, and the chosen actual root.
Q and Q' may be the supplied twisted point and twisted lift component. -/
def coordinateSet (d k : F) (s : Fb) (X U V W T R : P d) (Q Q' : P (k*d)) : Finset Fb :=
  insert s (coordinates X ∪ coordinates U ∪ coordinates V ∪ coordinates W ∪
    coordinates T ∪ coordinates R ∪ coordinates (X-T) ∪ coordinates (V-R) ∪
    coordinates Q ∪ coordinates Q')

theorem orbit_eq_of_fibre (d : F) (Q : P d) (S : Finset Fb)
    (hQ : coordinates Q ⊆ S) (g h : Gal)
    (he : restriction S g = restriction S h) :
    pointRho d (asAlg g) Q = pointRho d (asAlg h) Q := by
  cases Q with
  | zero =>
    change pointRho d (asAlg g) 0 = pointRho d (asAlg h) 0
    simp only [map_zero]
  | some x y N =>
    have hx : x ∈ S := hQ (by simp [coordinates])
    have hy : y ∈ S := hQ (by simp [coordinates])
    obtain ⟨Ng,eg⟩ := pointRho_some d (asAlg g) x y N
    obtain ⟨Nh,eh⟩ := pointRho_some d (asAlg h) x y N
    rw [eg,eh]
    simp [WeierstrassCurve.Affine.Point.some.injEq,
      restriction_same_coordinate S g h he hx,restriction_same_coordinate S g h he hy]

theorem bit_eq_of_fibre (s : Fb) (S : Finset Fb) (hs : s ∈ S) (g h : Gal)
    (he : restriction S g = restriction S h) :
    rootFlip s (asAlg g) = rootFlip s (asAlg h) := by
  unfold rootFlip
  rw [restriction_same_coordinate S g h he hs]

def phiAbs (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k) (hs0 : s ≠ 0)
    (X T : P d) (g : Gal) : P d × P d :=
  phiBoundary (actualAction d k s hs hs0) X T (asAlg g)

def psiAbs (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k) (hs0 : s ≠ 0)
    (V R : P d) (g : Gal) : P d × P d :=
  psiBoundary (actualAction d k s hs hs0) V R (asAlg g)

theorem phi_eq_on_fibre (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (X T : P d) (S : Finset Fb) (hS : s ∈ S)
    (hT : coordinates T ⊆ S) (hXT : coordinates (X-T) ⊆ S)
    (g h : Gal) (he : restriction S g = restriction S h) :
    phiAbs d k s hs hs0 X T g = phiAbs d k s hs hs0 X T h := by
  simp only [phiAbs,phiBoundary,OrderedAction.source,phiLift,actualAction,
    bit_eq_of_fibre s S hS g h he,orbit_eq_of_fibre d T S hT g h he,
    orbit_eq_of_fibre d (X-T) S hXT g h he]

theorem psi_eq_on_fibre (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (V R : P d) (S : Finset Fb) (hS : s ∈ S)
    (hR : coordinates R ⊆ S) (hVR : coordinates (V-R) ⊆ S)
    (g h : Gal) (he : restriction S g = restriction S h) :
    psiAbs d k s hs hs0 V R g = psiAbs d k s hs hs0 V R h := by
  simp only [psiAbs,psiBoundary,OrderedAction.target,psiLift,actualAction,
    bit_eq_of_fibre s S hS g h he,orbit_eq_of_fibre d R S hR g h he,
    orbit_eq_of_fibre d (V-R) S hVR g h he]

/-- A single literal finite Galois field contains the whole selected
coordinate list; both original cochains descend along its restriction. -/
theorem both_original_fibres (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (X U V W T R : P d) (Q Q' : P (k*d)) :
    let S := coordinateSet d k s X U V W T R Q Q'
    ∀ (g h : Gal), restriction S g=restriction S h →
      phiAbs d k s hs hs0 X T g = phiAbs d k s hs hs0 X T h ∧
      psiAbs d k s hs hs0 V R g = psiAbs d k s hs hs0 V R h := by
  let S := coordinateSet d k s X U V W T R Q Q'
  intro g h he
  have hS : s ∈ S := by simp [S,coordinateSet]
  refine ⟨phi_eq_on_fibre d k s hs hs0 X T S hS ?_ ?_ g h he,
    psi_eq_on_fibre d k s hs hs0 V R S hS ?_ ?_ g h he⟩ <;>
      intro a ha <;> simp [S,coordinateSet,ha]

theorem original_common_factor (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (X U V W T R : P d) (Q Q' : P (k*d)) :
    let S := coordinateSet d k s X U V W T R Q Q'
    ∃ phi psi : Auto S → P d × P d, ∀ g : Gal,
      phi (restriction S g)=phiAbs d k s hs hs0 X T g ∧
      psi (restriction S g)=psiAbs d k s hs hs0 V R g := by
  let S := coordinateSet d k s X U V W T R Q Q'
  refine ⟨factor S _,factor S _,fun g => ⟨factor_eval S _ ?_ g,factor_eval S _ ?_ g⟩⟩
  · exact fun g h he => (both_original_fibres d k s hs hs0 X U V W T R Q Q' g h he).1
  · exact fun g h he => (both_original_fibres d k s hs hs0 X U V W T R Q Q' g h he).2

theorem actual_locallyConstant (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (X U V W T R : P d) (Q Q' : P (k*d)) :
    IsLocallyConstant (phiAbs d k s hs hs0 X T) ∧
      IsLocallyConstant (psiAbs d k s hs hs0 V R) := by
  let S := coordinateSet d k s X U V W T R Q Q'
  refine ⟨locallyConstant_of_fibres S _ ?_,locallyConstant_of_fibres S _ ?_⟩
  · exact fun g h he => (both_original_fibres d k s hs hs0 X U V W T R Q Q' g h he).1
  · exact fun g h he => (both_original_fibres d k s hs hs0 X U V W T R Q Q' g h he).2

end OriginalRCMilneActualKummerContinuity318

#print axioms OriginalRCMilneActualKummerContinuity318.both_original_fibres
#print axioms OriginalRCMilneActualKummerContinuity318.actual_locallyConstant
