module
public import ComplexOpenPointEvaluation318
public section
noncomputable section
namespace ComplexBilinearOpenCoefficients318
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} (π : Y ⟶ Spec (CommRingCat.of ℂ))
@[expose] def scalar (W : Y.Opens) (c : ℂ) : Γ(Y,W) :=
  Y.presheaf.map (homOfLE (show W≤⊤ from le_top)).op
    (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
lemma scalar_evaluation (W : Y.Opens) (c : ℂ)
    (p : Spec (CommRingCat.of ℂ) ⟶ W.toScheme) (hp : p≫W.ι≫π=𝟙 _) :
    ComplexOpenPointEvaluation318.evaluation W p (scalar π W c)=c := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop W).inv _))=_
  have hr (r : Γ(Y,⊤)) : (LineFrameTopScalar318.ringTop W).inv
      (Y.presheaf.map (homOfLE le_top).op r)=W.ι.appTop r := by
    rw [Scheme.Opens.ι_appTop]
    change Y.presheaf.map _ (Y.presheaf.map _ r)=_
    rw [←Functor.map_comp]
    rfl
  rw [scalar,hr]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((p≫W.ι≫π).appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))=_
  rw [hp]
  simpa only [Scheme.Hom.id_appTop,CommRingCat.id_apply] using
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply c

variable (f g : Y ⟶ X) (U V : X.Opens)
abbrev domain := (f ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V)
@[expose] def left (r : Γ(X,U)) : Γ(Y,domain f g U V) :=
  Y.presheaf.map (homOfLE (show domain f g U V≤f ⁻¹ᵁ U from inf_le_left)).op (f.app U r)
@[expose] def right (s : Γ(X,V)) : Γ(Y,domain f g U V) :=
  Y.presheaf.map (homOfLE (show domain f g U V≤g ⁻¹ᵁ V from inf_le_right)).op (g.app V s)

lemma left_evaluation (r : Γ(X,U))
    (p : Spec (CommRingCat.of ℂ) ⟶ (domain f g U V).toScheme)
    (q : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (hp : p≫(domain f g U V).ι≫f=q≫U.ι) :
    ComplexOpenPointEvaluation318.evaluation (domain f g U V) p (left f g U V r)=
      ComplexOpenPointEvaluation318.evaluation U q r := by
  rw [left,ComplexOpenPointEvaluation318.restriction]
  apply ComplexOpenPointEvaluation318.pullback f U _ q _ r
  simpa only [Category.assoc,Scheme.homOfLE_ι_assoc] using hp
lemma right_evaluation (s : Γ(X,V))
    (p : Spec (CommRingCat.of ℂ) ⟶ (domain f g U V).toScheme)
    (q : Spec (CommRingCat.of ℂ) ⟶ V.toScheme)
    (hp : p≫(domain f g U V).ι≫g=q≫V.ι) :
    ComplexOpenPointEvaluation318.evaluation (domain f g U V) p (right f g U V s)=
      ComplexOpenPointEvaluation318.evaluation V q s := by
  rw [right,ComplexOpenPointEvaluation318.restriction]
  apply ComplexOpenPointEvaluation318.pullback g V _ q _ s
  simpa only [Category.assoc,Scheme.homOfLE_ι_assoc] using hp

variable {I J : Type} [Fintype I] [Fintype J]
@[expose] def sum (C : I → J → ℂ) (r : I → Γ(X,U)) (s : J → Γ(X,V)) :
    Γ(Y,domain f g U V) :=
  ∑ i,∑ j,scalar π (domain f g U V) (C i j)*left f g U V (r i)*right f g U V (s j)

/-- Finite constant double expansion is evaluated through the actual
base scalar map and both actual restricted structure-sheaf maps. -/
lemma sum_evaluation (C : I → J → ℂ) (r : I → Γ(X,U)) (s : J → Γ(X,V))
    (p : Spec (CommRingCat.of ℂ) ⟶ (domain f g U V).toScheme)
    (pC : p≫(domain f g U V).ι≫π=𝟙 _)
    (q : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (t : Spec (CommRingCat.of ℂ) ⟶ V.toScheme)
    (hq : p≫(domain f g U V).ι≫f=q≫U.ι)
    (ht : p≫(domain f g U V).ι≫g=t≫V.ι) :
    ComplexOpenPointEvaluation318.evaluation (domain f g U V) p (sum π f g U V C r s)=
      ∑ i,∑ j,C i j*ComplexOpenPointEvaluation318.evaluation U q (r i)*
        ComplexOpenPointEvaluation318.evaluation V t (s j) := by
  simp only [sum,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [scalar_evaluation π _ _ p pC,left_evaluation f g U V _ p q hq,
    right_evaluation f g U V _ p t ht]
end ComplexBilinearOpenCoefficients318
