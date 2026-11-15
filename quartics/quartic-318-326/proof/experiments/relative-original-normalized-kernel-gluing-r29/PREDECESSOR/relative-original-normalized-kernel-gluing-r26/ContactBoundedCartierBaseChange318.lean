module
public import RelativeCartierSchemeCartesian318
public import ContactBoundedCartierEquiv318
public section
noncomputable section
namespace ContactBoundedCartierBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B T : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (g : T ⟶ B) (hg : g ≫ b=t)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- The genuine original bounded Cartier domain is now stable under
ALL scheme coefficient maps, through its actual full ideal comap. -/
@[expose] def map (D : ContactBoundedCartierEquiv318.Data c N b) :
    ContactBoundedCartierEquiv318.Data c N t :=
  ⟨ContactBoundedHilbertBaseChange318.map c N b t g hg D.val,
    RelativeCartierSchemeCartesian318.regular D.val.ideal.subschemeι (pullback.snd p b) g
      _ _ _ (pullback.snd p t)
      (IdealSheafCoefficientCartesian318.cartesian D.val.ideal
        (RelativeSchemeCoefficient318.map p b t g hg))
      (RelativeSchemeCoefficient318.cartesian p b t g hg) D.property⟩
lemma ideal (D : ContactBoundedCartierEquiv318.Data c N b) :
    (map c N b t g hg D).val.ideal=D.val.ideal.comap (RelativeSchemeCoefficient318.map p b t g hg) := rfl
lemma underlying (D : ContactBoundedCartierEquiv318.Data c N b) :
    (map c N b t g hg D).val=ContactBoundedHilbertBaseChange318.map c N b t g hg D.val := rfl
end ContactBoundedCartierBaseChange318
