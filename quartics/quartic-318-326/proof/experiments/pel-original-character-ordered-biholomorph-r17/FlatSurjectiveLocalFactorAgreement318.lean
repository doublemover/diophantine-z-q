module
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace FlatSurjectiveLocalFactorAgreement318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y Z:Scheme.{u}} (f:X⟶Y) [Flat f] [Surjective f]

/-- Overlap agreement is PRODUCED by cancellation of the actual flat
surjective restricted morphism, not assumed as a quotient descent datum. -/
theorem overlap (g:X⟶Z) (U V:Y.Opens) (F:U.toScheme⟶Z) (G:V.toScheme⟶Z)
    (hF:(f ∣_ U)≫F=(f⁻¹ᵁU).ι≫g) (hG:(f ∣_ V)≫G=(f⁻¹ᵁV).ι≫g):
    Y.homOfLE (U:=U⊓V) inf_le_left≫F=Y.homOfLE (U:=U⊓V) inf_le_right≫G:=by
  letI:Epi (f ∣_ (U⊓V)):=Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (f ∣_ (U⊓V))).mp
  calc
    _=(X.homOfLE (f.preimage_mono inf_le_left)≫(f ∣_ U))≫F:=by
      rw [←Category.assoc,morphismRestrict_homOfLE]
    _=(f⁻¹ᵁ(U⊓V)).ι≫g:=by
      rw [Category.assoc,hF,←Category.assoc,Scheme.homOfLE_ι]
    _=(X.homOfLE (f.preimage_mono inf_le_right)≫(f ∣_ V))≫G:=by
      rw [Category.assoc,hG,←Category.assoc,Scheme.homOfLE_ι]
    _=_:=by rw [←morphismRestrict_homOfLE,Category.assoc]

lemma pullback_compatibility (g:X⟶Z) (U V:Y.Opens) (F:U.toScheme⟶Z) (G:V.toScheme⟶Z)
    (hF:(f ∣_ U)≫F=(f⁻¹ᵁU).ι≫g) (hG:(f ∣_ V)≫G=(f⁻¹ᵁV).ι≫g):
    pullback.fst U.ι V.ι≫F=pullback.snd U.ι V.ι≫G:=by
  let h:=isPullback_opens_inf U V
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [←Category.assoc,h.isoPullback_hom_fst,h.isoPullback_hom_snd] using
    overlap f g U V F G hF hG
end FlatSurjectiveLocalFactorAgreement318
