module
public import InverseImageLocalCohomology318
public import OpenMayerVietoris318

public section
noncomputable section
namespace InverseImageMayerVietoris318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 SheafInverseImageConstants318
open InverseImageLocalGenerator318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : TopCat.{0}} (f : X ⟶ Y) (U V : Opens Y) (h : U ⊔ V = ⊤)

include h in
theorem inverseImage_cover : (Opens.map f).obj U ⊔ (Opens.map f).obj V = ⊤ := by
  apply top_unique
  intro x hx
  have hm : f x ∈ U ⊔ V := by rw [h]; trivial
  exact hm

abbrev targetSquare := OpenMayerVietoris318.mayerVietoris U V h
abbrev sourceSquare := OpenMayerVietoris318.mayerVietoris
  ((Opens.map f).obj U) ((Opens.map f).obj V) (inverseImage_cover f U V h)

/-- The middle generator comparison retains both chart summands in their original order. -/
@[expose] def middleMap :
    (sourceSquare f U V h).shortComplex.X₂ ⟶
      (inverseImage f).obj (targetSquare U V h).shortComplex.X₂ :=
  biprod.desc
    (generatorInv f U ≫ (inverseImage f).map biprod.inl)
    (generatorInv f V ≫ (inverseImage f).map biprod.inr)

/-- The exact original two-chart generator sequence maps to the inverse image of the target sequence. -/
@[expose] def shortComplexMap : (sourceSquare f U V h).shortComplex ⟶
    ((targetSquare U V h).shortComplex.map (inverseImage f)) where
  τ₁ := generatorInv f (U ⊓ V)
  τ₂ := middleMap f U V h
  τ₃ := generatorInv f ⊤
  comm₁₂ := by
    change generatorInv f (U ⊓ V) ≫ (inverseImage f).map
      (biprod.lift (LocalCohomologyRestriction318.generatorMap
        (homOfLE inf_le_left : U ⊓ V ⟶ U))
        (-LocalCohomologyRestriction318.generatorMap
        (homOfLE inf_le_right : U ⊓ V ⟶ V))) =
      biprod.lift (LocalCohomologyRestriction318.generatorMap
        ((Opens.map f).map (homOfLE inf_le_left : U ⊓ V ⟶ U)))
        (-LocalCohomologyRestriction318.generatorMap
        ((Opens.map f).map (homOfLE inf_le_right : U ⊓ V ⟶ V))) ≫ _
    simp only [middleMap,biprod.lift_eq,Functor.map_add,Functor.map_neg,Functor.map_comp,
      Preadditive.comp_add,Preadditive.add_comp,Preadditive.comp_neg,Preadditive.neg_comp,
      Category.assoc,biprod.inl_desc,biprod.inr_desc]
    simp only [← Category.assoc,← generatorInv_naturality]
    all_goals rfl
  comm₂₃ := by
    apply biprod.hom_ext'
    · change biprod.inl ≫ middleMap f U V h ≫ (inverseImage f).map
        (biprod.desc (LocalCohomologyRestriction318.generatorMap
          (homOfLE le_top : U ⟶ ⊤)) (LocalCohomologyRestriction318.generatorMap
          (homOfLE le_top : V ⟶ ⊤))) =
        biprod.inl ≫ biprod.desc
          (LocalCohomologyRestriction318.generatorMap
            ((Opens.map f).map (homOfLE le_top : U ⟶ ⊤)))
          (LocalCohomologyRestriction318.generatorMap
            ((Opens.map f).map (homOfLE le_top : V ⟶ ⊤))) ≫ generatorInv f ⊤
      simp only [middleMap,biprod.inl_desc_assoc,← Functor.map_comp,Category.assoc,
        biprod.inl_desc]
      exact (generatorInv_naturality f (homOfLE le_top : U ⟶ ⊤)).symm
    · change biprod.inr ≫ middleMap f U V h ≫ (inverseImage f).map
        (biprod.desc (LocalCohomologyRestriction318.generatorMap
          (homOfLE le_top : U ⟶ ⊤)) (LocalCohomologyRestriction318.generatorMap
          (homOfLE le_top : V ⟶ ⊤))) =
        biprod.inr ≫ biprod.desc
          (LocalCohomologyRestriction318.generatorMap
            ((Opens.map f).map (homOfLE le_top : U ⟶ ⊤)))
          (LocalCohomologyRestriction318.generatorMap
            ((Opens.map f).map (homOfLE le_top : V ⟶ ⊤))) ≫ generatorInv f ⊤
      simp only [middleMap,biprod.inr_desc_assoc,← Functor.map_comp,Category.assoc,
        biprod.inr_desc]
      exact (generatorInv_naturality f (homOfLE le_top : V ⟶ ⊤)).symm

/-- The actual extension class, including its difference sign, commutes with inverse image. -/
theorem extClass_naturality :
    (sourceSquare f U V h).shortComplex_shortExact.extClass.comp
        (Ext.mk₀ (generatorInv f (U ⊓ V))) (add_zero 1) =
      (Ext.mk₀ (generatorInv f ⊤)).comp
        ((targetSquare U V h).shortComplex_shortExact.extClass.mapExactFunctor (inverseImage f))
        (zero_add 1) := by
  rw [Ext.mapExactFunctor_extClass]
  exact ShortComplex.ShortExact.extClass_naturality
    (sourceSquare f U V h).shortComplex_shortExact
    ((targetSquare U V h).shortComplex_shortExact.map_of_exact (inverseImage f))
    (shortComplexMap f U V h)

/-- Naturality of the genuine local Mayer–Vietoris boundary under the original derived comparison. -/
theorem delta_comparison (F : ASheaf (X:=X))
    (x : ((directImage f).obj F).H' 0 (U ⊓ V)) :
    InverseImageLocalCohomology318.comparison f F ⊤ 1
        ((targetSquare U V h).δ ((directImage f).obj F) 0 1 rfl x) =
      (sourceSquare f U V h).δ F 0 1 rfl
        (InverseImageLocalCohomology318.comparison f F (U ⊓ V) 0 x) := by
  change (Ext.mk₀ (generatorInv f ⊤)).comp
      ((((targetSquare U V h).shortComplex_shortExact.extClass.comp x (by decide)).mapExactFunctor
        (inverseImage f)).comp (Ext.mk₀ ((adjunction f).counit.app F)) (add_zero 1))
      (zero_add 1) =
    (sourceSquare f U V h).shortComplex_shortExact.extClass.comp
      ((Ext.mk₀ (generatorInv f (U ⊓ V))).comp
        ((x.mapExactFunctor (inverseImage f)).comp
          (Ext.mk₀ ((adjunction f).counit.app F)) (add_zero 0)) (zero_add 0)) (by decide)
  rw [Ext.mapExactFunctor_comp]
  simp only [← Ext.comp_assoc_of_second_deg_zero,← Ext.comp_assoc_of_third_deg_zero]
  rw [extClass_naturality]

end InverseImageMayerVietoris318
