module
public import ContactPositiveDifferencePresentation318
public section
noncomputable section
namespace RelativeAmbientReassociationInverse318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {C S R B T : Scheme.{u}} (p : C ⟶ S) (r : R ⟶ S) (b : B ⟶ R)
local notation "q" => pullback.snd p r
local notation "e" => RelativeAmbientReassociation318.comparison p r b
@[reassoc] lemma second : e.inv ≫ pullback.snd q b=pullback.snd p (b ≫ r) := by
  rw [←RelativeAmbientReassociation318.second p r b]
  simp only [←Category.assoc,Iso.inv_hom_id,Category.id_comp]
@[reassoc] lemma original : e.inv ≫ RelativeAmbientReassociation318.original p r b=pullback.fst p (b ≫ r) := by
  rw [←RelativeAmbientReassociation318.first p r b]
  simp only [←Category.assoc,Iso.inv_hom_id,Category.id_comp]
/-- The inverse reassociation followed by the original relative-curve
projection is precisely the existing literal coefficient map. -/
lemma relative_projection : e.inv ≫ pullback.fst q b=
    RelativeLineClassBaseChange318.totalMap p r (b ≫ r) b rfl := by
  apply pullback.hom_ext
  · simpa only [Category.assoc,RelativeAmbientReassociation318.original,
      RelativeLineClassBaseChange318.totalMap_fst] using original p r b
  · calc
      _ = e.inv ≫ (pullback.snd q b ≫ b) := by rw [Category.assoc,pullback.condition]
      _ = pullback.snd p (b ≫ r) ≫ b := by rw [←Category.assoc,second]
      _ = _ := (RelativeLineClassBaseChange318.totalMap_snd p r (b ≫ r) b rfl).symm
lemma natural (t : T ⟶ R) (j : T ⟶ B) (hj : j ≫ b=t) :
    (RelativeAmbientReassociation318.comparison p r t).inv ≫ RelativeSchemeCoefficient318.map q b t j hj=
      RelativeSchemeCoefficient318.map p (b ≫ r) (t ≫ r) j (by rw [←Category.assoc,hj]) ≫ e.inv := by
  let eT := RelativeAmbientReassociation318.comparison p r t
  let f := RelativeSchemeCoefficient318.map q b t j hj
  let g := RelativeSchemeCoefficient318.map p (b ≫ r) (t ≫ r) j (by rw [←Category.assoc,hj])
  have h : f ≫ e.hom=eT.hom ≫ g := RelativeAmbientReassociation318.natural p r b t j hj
  calc
    eT.inv ≫ f = eT.inv ≫ (f ≫ e.hom) ≫ e.inv := by
      simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    _ = eT.inv ≫ (eT.hom ≫ g) ≫ e.inv := congrArg (fun k => eT.inv ≫ k ≫ e.inv) h
    _ = _ := by simp only [←Category.assoc,Iso.inv_hom_id,Category.id_comp]
end RelativeAmbientReassociationInverse318
