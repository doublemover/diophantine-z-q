module
public import OpenAffineTargetFactorization318
public import PELOriginalLocalTargetSchemeMaps318
public section
noncomputable section
namespace PELOriginalLocalSchemeFactorization318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
open PELOriginalInvariantMapOpenDescent318 PELOriginalLocalTargetRingMaps318
open PELOriginalLocalTargetSchemeMaps318
variable {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
  (hg:∀a:Kernel i,schemeDeck a.val≫g=g) (V:Z.Opens) (hV:IsAffineOpen V)

/-- Exact original local factorization AS SCHEME MORPHISMS, not merely
on coordinates, points, generic germs or a record of assumed equations. -/
theorem local_factor:
    (morphism i).resLE (descendedOpen i g hg V)
      (morphism i⁻¹ᵁ(descendedOpen i g hg V)) le_rfl≫localMap i g hg V hV=
    g.resLE V (morphism i⁻¹ᵁ(descendedOpen i g hg V))
      (preimage_descendedOpen i g hg V).le:=
  OpenAffineTargetFactorization318.resLE_factor (morphism i) g _ V hV _
    (targetRingMap i g hg V) (targetRingMap_square i g hg V)

theorem local_factor_to_target:
    (morphism i).resLE (descendedOpen i g hg V)
      (morphism i⁻¹ᵁ(descendedOpen i g hg V)) le_rfl≫localMapToTarget i g hg V hV=
    (morphism i⁻¹ᵁ(descendedOpen i g hg V)).ι≫g:=
  OpenAffineTargetFactorization318.target_factor (morphism i) g _ V hV _
    (targetRingMap i g hg V) (targetRingMap_square i g hg V)

lemma restricted_factor_to_target:
    (morphism i ∣_ descendedOpen i g hg V)≫localMapToTarget i g hg V hV=
      (morphism i⁻¹ᵁ(descendedOpen i g hg V)).ι≫g:=by
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using local_factor_to_target i g hg V hV

end PELOriginalLocalSchemeFactorization318
