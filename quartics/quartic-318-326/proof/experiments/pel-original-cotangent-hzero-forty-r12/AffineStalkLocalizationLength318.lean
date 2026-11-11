module
public import AffineTildeQuotientStalk318
public import LocalIdealLengthTransport318
public section
noncomputable section
namespace AffineStalkLocalizationLength318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
/-- The canonical structure-sheaf stalk isomorphism retains every
original coefficient, so it transports the SAME mapped ideal. -/
lemma full_ideal :
    I.map (algebraMap R (Localization.AtPrime p.asIdeal)) =
      (AffineTildeQuotientStalk318.localIdeal R I p).map
        (StructureSheaf.stalkIso R p).symm.toRingEquiv.toRingHom := by
  rw [AffineTildeQuotientStalk318.localIdeal,Ideal.map_map]
  congr 1
  ext r
  exact ((StructureSheaf.stalkIso R p).symm.commutes r).symm
/-- Exact length comparison over actual local rings and canonical
localizations, with no assumptions on prime, ideal or residue field. -/
theorem length_eq :
    Module.length (AffineTildeQuotientStalk318.LocalRing R p)
      (AffineTildeQuotientStalk318.LocalRing R p ⧸
        AffineTildeQuotientStalk318.localIdeal R I p) =
    Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap R _)) :=
  LocalIdealLengthTransport318.quotient_length
    (StructureSheaf.stalkIso R p).symm.toRingEquiv _ _ (full_ideal R I p)
end AffineStalkLocalizationLength318
