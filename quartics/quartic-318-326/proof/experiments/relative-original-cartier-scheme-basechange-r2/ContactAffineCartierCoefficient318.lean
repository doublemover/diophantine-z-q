module
public import RelativeCartierAffineCartesian318
public import ContactBoundedCartierEquiv318
public section
noncomputable section
namespace ContactAffineCartierCoefficient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) (R S : CommRingCat.{0}) [Algebra R S]
  (b : Spec R ⟶ Spec (CommRingCat.of ℚ))
local notation "f" => RelativeOriginalAffineChart318.baseMap R S
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "t" => f ≫ b
/-- The genuine bounded Cartier domain is closed under EVERY affine
coefficient change. This uses flatness of the actual whole Hilbert
family and retains its full ideal comap, with no flatness of S/R. -/
@[expose] def map (D : ContactBoundedCartierEquiv318.Data c N b) :
    ContactBoundedCartierEquiv318.Data c N t :=
  ⟨ContactBoundedHilbertBaseChange318.map c N b t f rfl D.val,by
    exact RelativeCartierAffineCartesian318.regular R S D.val.ideal.subschemeι
      (pullback.snd p b) _ _ _ (pullback.snd p t)
      (IdealSheafCoefficientCartesian318.cartesian D.val.ideal
        (RelativeSchemeCoefficient318.map p b t f rfl))
      (RelativeSchemeCoefficient318.cartesian p b t f rfl) D.property⟩
lemma ideal (D : ContactBoundedCartierEquiv318.Data c N b) :
    (map c N R S b D).val.ideal=D.val.ideal.comap (RelativeSchemeCoefficient318.map p b t f rfl) := rfl
/-- The restricted classifier still sends the actual complete coefficient
family to the same standard bounded parameter point. -/
lemma underlying (D : ContactBoundedCartierEquiv318.Data c N b) :
    (ContactBoundedCartierEquiv318.forward c N t (map c N R S b D)).val=
      ContactBoundedHilbertEquiv318.equivalence c N t
        (ContactBoundedHilbertBaseChange318.map c N b t f rfl D.val) := rfl
end ContactAffineCartierCoefficient318
