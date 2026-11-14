module
public import OriginalRelativeClassIso318
public section
noncomputable section
namespace OriginalOpenRelativeClasses318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 RelativeLineClassQuotient318 OriginalOpenFamilyTest318
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (U : T.Opens)

/-- Full-test classes and classes on the exact inverse-image open are
identified by the original two relative pullback maps of its actual iso. -/
@[expose] def equivalence : TestClass q (U.ι ≫ b) ≃* RelativeClass (projection q b ∣_ U) :=
  OriginalRelativeClassIso318.equivalence (pullback.snd q (U.ι ≫ b)) (projection q b ∣_ U)
    (OriginalOpenFamilyTest318.iso q b U).symm (by
      rw [Category.comp_id]
      exact iso_inv_projection q b U)

/-- Exact original relative restriction to the inverse-image open. -/
@[expose] def restriction : TestClass q b →* RelativeClass (projection q b ∣_ U) :=
  RelativeLineClassQuotient318.map (projection q b) (projection q b ∣_ U)
    (sourceOpen q b U).ι U.ι (morphismRestrict_ι (projection q b) U).symm

lemma restriction_eq (c : TestClass q b) :
    equivalence q b U (testMap q b (U.ι ≫ b) U.ι rfl c) = restriction q b U c := by
  have h := RelativeLineClassQuotient318.map_composition (projection q b)
    (pullback.snd q (U.ι ≫ b)) (projection q b ∣_ U)
    (total q b U) U.ι (OriginalOpenFamilyTest318.iso q b U).inv (𝟙 _)
    (totalMap_snd q b (U.ι ≫ b) U.ι rfl) (by
      rw [Category.comp_id]
      exact iso_inv_projection q b U) (by
      rw [iso_inv_total,Category.id_comp]
      exact (morphismRestrict_ι (projection q b) U).symm)
  have hh := congrArg (fun k => k c) h
  simpa only [iso_inv_total,Category.id_comp,MonoidHom.comp_apply] using hh.symm
end OriginalOpenRelativeClasses318
