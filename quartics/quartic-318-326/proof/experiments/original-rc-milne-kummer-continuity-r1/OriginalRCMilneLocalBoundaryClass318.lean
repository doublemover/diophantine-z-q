module
public import OriginalRCMilneActualKummerContinuity318
import all OriginalRCMilneActualKummerContinuity318
import all OriginalRCMilneTwistedKummerPointAction318
import all Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Tactic.Abel

public section
noncomputable section

namespace OriginalRCMilneLocalBoundaryClass318

open ActualTwoDescentEllipticModel318 OriginalRCMilneFiniteGaloisLayer318
open OriginalRCMilneTwistedKummerCore318 OriginalRCMilneTwistedKummerPointAction318
open OriginalRCMilneActualTwistedKummer318 OriginalRCMilneActualKummerContinuity318

variable {F : Type*} [Field F] [CharZero F]
local notation "Fb" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Fb := Classical.decEq _
local notation "P" d => Point (algebraMap F Fb d)

abbrev Two (d : F) := (OriginalRCMilneSplitLocal318.twice (P d)).ker

/-- An explicit locally constant representative on the literal kernel.
On these two-torsion points the action is trivial, so there are no
nonzero degree-one coboundaries to quotient by. This is the local
boundary class model; it is not a global H¹ or Poitou–Tate object. -/
structure LocalClass (d : F) where
  value : LocallyConstant Gal (Two d)
  mul_add : ∀ g h, value (g*h) = value g + value h

theorem source_fixed (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (g : Gal) (Y : P d) (hy : Y+Y=0) :
    (actualAction d k s hs hs0).source (asAlg g) (Y,Y)=(Y,Y) := by
  cases h : rootFlip s (asAlg g) <;>
    simp [OrderedAction.source,actualAction,h,actual_two_fixed d (asAlg g) Y hy]

theorem target_fixed (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (g : Gal) (Y : P d) (hy : Y+Y=0) :
    (actualAction d k s hs hs0).target (asAlg g) (Y,Y)=(Y,Y) := by
  have hneg : -Y=Y := by
    calc
      _ = (Y+Y)-Y := by rw [hy,zero_sub]
      _ = _ := by abel
  cases h : rootFlip s (asAlg g) <;>
    simp [OrderedAction.target,actualAction,h,actual_two_fixed d (asAlg g) Y hy,hneg]

def classOfPair (d : F) (z : Gal → P d × P d) (hLC : IsLocallyConstant z)
    (hTwo : ∀ g, (z g).1+(z g).1=0)
    (hAdd : ∀ g h, z (g*h)=z g+z h) : LocalClass d where
  value :=
    ⟨fun g => ⟨(z g).1,hTwo g⟩,by
      apply (IsLocallyConstant.iff_exists_open _).mpr
      intro g
      obtain ⟨U,hU,hg,he⟩ := (IsLocallyConstant.iff_exists_open _).mp hLC g
      exact ⟨U,hU,hg,fun h hh => Subtype.ext (congrArg Prod.fst (he h hh))⟩⟩
  mul_add g h := Subtype.ext (congrArg Prod.fst (hAdd g h))

theorem phiDiag (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (hd : d ≠ 0) (hk : k ≠ 0) (X U T : P d)
    (hT : T+T=X+U) (hX : ∀ g : Gal, pointRho d (asAlg g) X=X)
    (hU : ∀ g : Gal, pointRho (k*d) (asAlg g) (twist d k s hs hs0 hd hk U)=
      twist d k s hs hs0 hd hk U) (g : Gal) :
    let z := phiAbs d k s hs hs0 X T g
    z=(z.1,z.1) ∧ z.1+z.1=0 := by
  obtain ⟨he,h₂⟩ := actual_phi_representative d k s hs hs0 hd hk (asAlg g)
    X U T hT (hX g) (hU g)
  change phiAbs d k s hs hs0 X T g =
    ((phiAbs d k s hs hs0 X T g).1,(phiAbs d k s hs hs0 X T g).1) ∧ _
  rw [phiAbs,he]
  exact ⟨rfl,h₂⟩

theorem psiDiag (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (V W R : P d) (hR : R+R=V-W)
    (hVW : ∀ g : Gal, (actualAction d k s hs hs0).source (asAlg g) (V,W)=(V,W)) (g : Gal) :
    let z := psiAbs d k s hs hs0 V R g
    z=(z.1,z.1) ∧ z.1+z.1=0 := by
  obtain ⟨he,h₂⟩ := actual_psi_representative d k s hs hs0 (asAlg g) V W R hR (hVW g)
  change psiAbs d k s hs hs0 V R g =
    ((psiAbs d k s hs hs0 V R g).1,(psiAbs d k s hs hs0 V R g).1) ∧ _
  rw [psiAbs,he]
  exact ⟨rfl,h₂⟩

/-- Consume the ONE joint field proof for both actual local boundaries,
preserving their input points, both original halves, and the twist
already attached to the second target coordinate. -/
def originalClasses (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (hd : d ≠ 0) (hk : k ≠ 0)
    (X U V W T R : P d) (hT : T+T=X+U) (hR : R+R=V-W)
    (hX : ∀ g : Gal, pointRho d (asAlg g) X=X)
    (hU : ∀ g : Gal, pointRho (k*d) (asAlg g) (twist d k s hs hs0 hd hk U)=
      twist d k s hs hs0 hd hk U)
    (hVW : ∀ g : Gal, (actualAction d k s hs hs0).source (asAlg g) (V,W)=(V,W)) :
    LocalClass d × LocalClass d := by
  let D := actualAction d k s hs hs0
  let i := twist d k s hs hs0 hd hk
  have lc := actual_locallyConstant d k s hs hs0 X U V W T R (i U) (i R)
  have hA := phiDiag d k s hs hs0 hd hk X U T hT hX hU
  have hB := psiDiag d k s hs hs0 V W R hR hVW
  refine ⟨classOfPair d _ lc.1 (fun g => (hA g).2) ?_,
    classOfPair d _ lc.2 (fun g => (hB g).2) ?_⟩
  · intro g h
    have hLaw : phiAbs d k s hs hs0 X T (g*h) = phiAbs d k s hs hs0 X T g +
        D.source (asAlg g) (phiAbs d k s hs hs0 X T h) :=
      phi_cocycle D X T (asAlg g) (asAlg h)
    have hf : D.source (asAlg g) (phiAbs d k s hs hs0 X T h)=phiAbs d k s hs hs0 X T h :=
      (congrArg (D.source (asAlg g)) (hA h).1).trans
        ((source_fixed d k s hs hs0 g _ (hA h).2).trans (hA h).1.symm)
    rwa [hf] at hLaw
  · intro g h
    have hLaw : psiAbs d k s hs hs0 V R (g*h) = psiAbs d k s hs hs0 V R g +
        D.target (asAlg g) (psiAbs d k s hs hs0 V R h) :=
      psi_cocycle D V R (asAlg g) (asAlg h)
    have hf : D.target (asAlg g) (psiAbs d k s hs hs0 V R h)=psiAbs d k s hs hs0 V R h :=
      (congrArg (D.target (asAlg g)) (hB h).1).trans
        ((target_fixed d k s hs hs0 g _ (hB h).2).trans (hB h).1.symm)
    rwa [hf] at hLaw

theorem psi_equal_on_halves (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (V W R R' : P d) (h : R+R=V-W) (h' : R'+R'=V-W) (g : Gal) :
    psiAbs d k s hs hs0 V R' g=psiAbs d k s hs hs0 V R g := by
  let D := actualAction d k s hs hs0
  obtain ⟨Z,hZ,he⟩ := actual_psi_independence d k s hs hs0 V W R R' h h'
  obtain ⟨hdiag,h₂⟩ := kernel_diagonal Z hZ
  have hfix : D.target (asAlg g) Z=Z :=
    (congrArg (D.target (asAlg g)) hdiag).trans
      ((target_fixed d k s hs hs0 g _ h₂).trans hdiag.symm)
  apply sub_eq_zero.mp
  change psiBoundary D V R' (asAlg g)-psiBoundary D V R (asAlg g)=0
  rw [he (asAlg g),hfix,sub_self]

end OriginalRCMilneLocalBoundaryClass318

#print axioms OriginalRCMilneLocalBoundaryClass318.originalClasses
#print axioms OriginalRCMilneLocalBoundaryClass318.psi_equal_on_halves
