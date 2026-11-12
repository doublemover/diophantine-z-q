module
public import ContactDifferenceBaseTwistRelation318
public section
noncomputable section
namespace ContactDifferenceQuotientPresheaf318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ)
local notation "F" => ContactCartierDifferencePresheaf318.presheaf c
local notation "a" => ContactCartierDifferenceAbel318.transformation c
/-- The quotient relation is the proved geometric local base-line
isomorphism relation on actual full-ideal divisor pairs. -/
@[expose] def setoid (T : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ) : Setoid (F.obj T) where
  r D E := ContactDifferenceBaseTwistRelation318.sieve c T.unop D E ∈
    RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ)) T.unop
  iseqv := ⟨fun D => (ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop D D).mp rfl,
    fun {D E} h => (ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop E D).mp
      ((ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop D E).mpr h).symm,
    fun {D E K} h k => (ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop D K).mp
      (((ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop D E).mpr h).trans
        ((ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop E K).mpr k))⟩
abbrev Object (T : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ) := Quotient (setoid c T)
lemma map_respects {T U : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ} (f : T ⟶ U)
    {D E : F.obj T} (h : (setoid c T).Rel D E) : (setoid c U).Rel (F.map f D) (F.map f E) := by
  apply (ContactDifferenceBaseTwistRelation318.abel_iff_covering c U.unop _ _).mp
  have he := (ContactDifferenceBaseTwistRelation318.abel_iff_covering c T.unop D E).mpr h
  have hd := ConcreteCategory.congr_hom (a.naturality f) D
  have hk := ConcreteCategory.congr_hom (a.naturality f) E
  exact hd.trans ((congrArg (fun x => ((RelativeFppfLineSheaf318.sheaf
    (ContactIntrinsicDifferentials318.structureMap c)).obj ⋙ forget CommGrpCat.{1}).map f x) he).trans hk.symm)
/-- The honest presheaf quotient with actual coefficient restriction,
not an asserted scheme quotient or a chosen Jacobian. -/
@[expose] def presheaf : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ ⥤ Type 1 where
  obj T := Object c T
  map f := Quotient.map (F.map f) (fun _ _ h => map_respects c f h)
  map_id T := by
    funext x
    induction x using Quotient.inductionOn with
    | h D =>
      change Quotient.mk (setoid c T) (F.map (𝟙 T) D)=Quotient.mk (setoid c T) D
      rw [Functor.map_id,types_id_apply]
  map_comp f g := by
    funext x
    induction x using Quotient.inductionOn with
    | h D =>
      change Quotient.mk _ (F.map (f ≫ g) D)=Quotient.mk _ (F.map g (F.map f D))
      rw [Functor.map_comp,types_comp_apply]
@[expose] def quotient : F ⟶ presheaf c where
  app T D := Quotient.mk (setoid c T) D
  naturality _ _ _ := rfl
end ContactDifferenceQuotientPresheaf318
