module
public import ContactHilbertUniversalRecovery318
public section
noncomputable section
namespace ContactSchemeHilbertLocalRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactSchemeHilbertData318.Data c n b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "U" => RelativeAffineTestCover318.cover ℚ b
@[expose] def point : ContactSchemePointFamily318.SchemePoint c n b :=
  ⟨ContactSchemeHilbertRule318.classify c n b D,ContactSchemeHilbertRule318.over c n b D⟩
variable (i : U.I₀)
local notation "S" => RelativeAffineTestCover318.ring ℚ b i
local notation "x" => RelativeAffineTestCover318.point ℚ b i
local notation "Di" => ContactSchemeHilbertTest318.data c n b D S x
local notation "f" => point c n b D
local notation "q" => ContactProjectiveUniversalGluing318.original c n
local notation "a" => ContactSchemeHilbertTest318.sourceMap c b S x
local notation "m" => ContactSchemePointFamily318.sourceMap c n b f
local notation "k" => ContactHilbertUniversalRecovery318.toFamily c n S Di
lemma outer : IsPullback k Di.val.ideal.subschemeι q (a ≫ m) := by
  rw [RelativeSchemeCoefficient318.comp,ContactSchemeHilbertRule318.evaluate c n b D S x]
  exact ContactHilbertUniversalRecovery318.cartesian c n S Di
@[expose] def map : Di.val.ideal.subscheme ⟶ ContactSchemePointFamily318.family c n b f :=
  PullbackIntermediateFactor318.lift k Di.val.ideal.subschemeι q a m (outer c n b D i)
    (ContactSchemePointFamily318.toFamily c n b f) (ContactSchemePointFamily318.into c n b f)
    (ContactSchemePointFamily318.cartesian c n b f)
@[reassoc] lemma source : map c n b D i ≫ ContactSchemePointFamily318.into c n b f=Di.val.ideal.subschemeι ≫ a :=
  PullbackIntermediateFactor318.lift_right _ _ _ _ _ _ _ _ _
lemma cartesian : IsPullback (map c n b D i) Di.val.ideal.subschemeι
    (ContactSchemePointFamily318.into c n b f) a :=
  PullbackIntermediateFactor318.cartesian _ _ _ _ _ _ _ _ _
end ContactSchemeHilbertLocalRecovery318
