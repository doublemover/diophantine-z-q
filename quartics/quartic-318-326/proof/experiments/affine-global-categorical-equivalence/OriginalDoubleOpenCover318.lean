module
public import ActualDoubleCartesian318
public section
noncomputable section
namespace OriginalDoubleOpenCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
abbrev source := (f ⁻¹ᵁ V).ι
abbrev covering := f ∣_ V
abbrev doubleMap := ActualDescentBaseChangeDiagram318.doubleMap f (covering f V)
  (source f V) V.ι (morphismRestrict_ι f V).symm
abbrev base : Double f ⟶ Y := first f ≫ f
abbrev baseOpen : (Double f).Opens := base f ⁻¹ᵁ V

lemma square : IsPullback (doubleMap f V) (first (covering f V) ≫ covering f V) (base f) V.ι :=
  ActualDoubleCartesian318.isPullback f (covering f V) (source f V) V.ι
    (morphismRestrict_ι f V).symm (isPullback_morphismRestrict f V).flip

/-- The original double of the restricted cover is precisely the whole
inverse-image base open in the original double scheme. -/
@[expose] def iso : Double (covering f V) ≅ (baseOpen f V).toScheme :=
  (square f V).isoPullback ≪≫ pullbackRestrictIsoRestrict (base f) V

@[reassoc] lemma iso_hom_ι : (iso f V).hom ≫ (baseOpen f V).ι = doubleMap f V := by
  simp only [iso,Iso.trans_hom,Category.assoc,pullbackRestrictIsoRestrict_hom_ι,
    IsPullback.isoPullback_hom_fst]

/-- Every point of the original double is covered by a whole original
restricted double indexed by an affine open of the base. -/
lemma cover : (⊤ : (Double f).Opens) ≤ iSup (fun U : Y.affineOpens => baseOpen f U.1) :=
  LinePullbackFrames318.preimage_cover (base f) (fun U : Y.affineOpens => U.1)
    (AffineMorphismGlobalLine318.cover (Y:=Y))
end OriginalDoubleOpenCover318
