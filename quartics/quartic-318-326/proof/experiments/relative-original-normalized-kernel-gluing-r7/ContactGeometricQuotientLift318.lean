module
public import ContactAbelUniversalIsomInvariant318
public section
noncomputable section
namespace ContactGeometricQuotientLift318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "A" => ContactCartierDifferencePresheaf318.presheaf c
local notation "V" => ContactDifferenceQuotientPresheaf318.presheaf c
variable (F : Sheaf J (Type 1)) (a : A ⟶ F.obj)
  (ha : ContactGeometricIsomInvariant318.Invariant c F a)
/-- Explicit quotient descent from invariance on the produced geometric
Isom schemes, with no presumed constancy on global Picard fibers. -/
@[expose] def lift : V ⟶ F.obj where
  app T := Quotient.lift (a.app T) (fun D E h =>
    ContactWholeGeometricKernelDescent318.kernel c F a ha T.unop D E
      ((ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop D E).mpr h))
  naturality T U f := by
    funext x
    induction x using Quotient.inductionOn with
    | h D => exact ConcreteCategory.congr_hom (a.naturality f) D
lemma factor : ContactDifferenceQuotientPresheaf318.quotient c ≫ lift c F a ha=a := rfl
/-- Uniqueness on the actual presheaf quotient follows by real quotient
induction, without assuming a geometric scheme quotient. -/
lemma unique (g : V ⟶ F.obj)
    (hg : ContactDifferenceQuotientPresheaf318.quotient c ≫ g=a) : g=lift c F a ha := by
  ext T x
  induction x using Quotient.inductionOn with
  | h D => exact ConcreteCategory.congr_hom (congrArg (fun n => n.app T) hg) D
end ContactGeometricQuotientLift318
