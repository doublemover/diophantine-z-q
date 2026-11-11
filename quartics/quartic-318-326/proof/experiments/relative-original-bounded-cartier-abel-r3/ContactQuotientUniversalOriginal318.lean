module
public import RelativeSchemeOpenChart318
public import VaryingGlobalFamilyPresentation318
public section
noncomputable section
namespace ContactQuotientUniversalOriginal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (a : Chart) (n : ℕ)
local notation "A" => ring c a
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
abbrev parameter := VaryingWordChartGluing318.scheme ℚ A (Fin n)
abbrev structureMap := VaryingWordParameterStructure318.structureMap ℚ A (Fin n)
abbrev family := VaryingWordFamilyGluing318.scheme ℚ A (Fin n)
abbrev projection := VaryingWordGlobalFamilyProjection318.projection ℚ A (Fin n)
abbrev curve := pullback p (structureMap c a n)
abbrev ambientInto : VaryingWordGlobalAmbient318.ambient ℚ A (Fin n) ⟶ curve c a n :=
  RelativeSchemeOpenChart318.into p (structureMap c a n) (original c a)
    (VaryingSourceCoefficientPullback318.base ℚ A)
    (ContactOriginalLinearOpenChart318.affine_over c a.form a.homogeneous)
instance ambient_open : IsOpenImmersion (ambientInto c a n) := inferInstance
/-- The ACTUAL universal affine-source quotient family is inserted into
the unchanged original projective curve over its ENTIRE parameter scheme. -/
@[expose] def into : family c a n ⟶ curve c a n :=
  VaryingWordGlobalAmbient318.into ℚ A (Fin n) ≫ ambientInto c a n
@[reassoc] lemma into_base : into c a n ≫ pullback.snd p (structureMap c a n)=projection c a n := by
  rw [into,Category.assoc,RelativeSchemeOpenChart318.into_base]
  exact VaryingWordGlobalAmbient318.into_projection ℚ A (Fin n)
@[reassoc] lemma into_original : into c a n ≫ pullback.fst p (structureMap c a n)=
    VaryingWordGlobalOriginalMap318.original ℚ A (Fin n) ≫ original c a := by
  rw [into,Category.assoc,RelativeSchemeOpenChart318.into_original,← Category.assoc,
    VaryingWordGlobalAmbient318.into_original]
instance separated : IsSeparated (pullback.snd p (structureMap c a n)) := by
  letI : IsProper p := (ContactGlobalProper318.proper_integral_extension c).2.2
  infer_instance
/-- Whole-family finiteness upgrades the actual open-chart insertion
to a globally CLOSED original projective family, without closing its support. -/
instance closed : IsClosedImmersion (into c a n) := by
  letI : IsFinite ((VaryingWordGlobalAmbient318.into ℚ A (Fin n) ≫ ambientInto c a n) ≫
      pullback.snd p (structureMap c a n)) := by
    change IsFinite (into c a n ≫ pullback.snd p (structureMap c a n))
    rw [into_base]
    infer_instance
  exact FiniteClosedInOpen318.closed (VaryingWordGlobalAmbient318.into ℚ A (Fin n))
    (ambientInto c a n) (pullback.snd p (structureMap c a n))
abbrev idealSheaf : (curve c a n).IdealSheafData := (into c a n).ker
end ContactQuotientUniversalOriginal318
