module
public import ContactSchemeUniversalRecovery318
public section
noncomputable section
namespace ContactBoundedInputLocalRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactBoundedSchemeHilbertData318.Data c N b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "U" => ContactBoundedRankCover318.cover c N b D
@[expose] def point : ContactBoundedPointFamily318.SchemePoint c N b :=
  ⟨ContactBoundedClassifyingMap318.classify c N b D,ContactBoundedClassifyingMap318.over c N b D⟩
variable (d : Fin (N+1))
local notation "a" => ContactBoundedRankData318.base c N b D d
local notation "Di" => ContactBoundedRankData318.data c N b D d
local notation "x" => ContactBoundedRankData318.point c N b D d
local notation "f" => point c N b D
local notation "s" => ContactBoundedHilbertParameter318.structureMap c N
local notation "r" => ContactBoundedUniversalFamily318.original c N
local notation "t" => ContactBoundedHilbertBaseChange318.sourceMap c b a (U.f d) rfl
local notation "m" => ContactBoundedPointFamily318.sourceMap c N b f
abbrev toUniversal : Di.ideal.subscheme ⟶ ContactBoundedHilbertParameter318.family c N :=
  ContactSchemeUniversalRecovery318.toFamily c d.val a Di ≫ ContactBoundedHilbertParameter318.familyInto c N d
/-- The local whole original family is Cartesian over the global bounded
universal family, retaining the literal rank-cover classifying evaluation. -/
lemma outer : IsPullback (toUniversal c N b D d) Di.ideal.subschemeι r (t ≫ m) := by
  have h := (ContactSchemeUniversalRecovery318.cartesian c d.val a Di).paste_horiz
    (ContactBoundedUniversalFamily318.cartesian c N d)
  rw [RelativeSchemeCoefficient318.comp] at h ⊢
  rw [ContactBoundedClassifyingMap318.evaluate]
  exact h
@[expose] def map : Di.ideal.subscheme ⟶ ContactBoundedPointFamily318.family c N b f :=
  PullbackIntermediateFactor318.lift (toUniversal c N b D d) Di.ideal.subschemeι r t m
    (outer c N b D d) (ContactBoundedPointFamily318.toFamily c N b f)
    (ContactBoundedPointFamily318.into c N b f) (ContactBoundedPointFamily318.cartesian c N b f)
@[reassoc] lemma source : map c N b D d ≫ ContactBoundedPointFamily318.into c N b f=Di.ideal.subschemeι ≫ t :=
  PullbackIntermediateFactor318.lift_right _ _ _ _ _ _ _ _ _
lemma cartesian : IsPullback (map c N b D d) Di.ideal.subschemeι (ContactBoundedPointFamily318.into c N b f) t :=
  PullbackIntermediateFactor318.cartesian _ _ _ _ _ _ _ _ _
end ContactBoundedInputLocalRecovery318
