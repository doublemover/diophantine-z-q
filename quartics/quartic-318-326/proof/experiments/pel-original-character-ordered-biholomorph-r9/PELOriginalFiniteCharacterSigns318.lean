module
public import PELOriginalDescendedOriginAction318
public section
noncomputable section
namespace PELOriginalFiniteCharacterSigns318
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalOrderedCharacterSchemeMaps318 PELOriginalActualCharacterFields318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open OriginalContactInertiaBasis318

lemma signed_x (i:Fin 4) (a:Labels):
    FourRootCoordinateRingSigns318.finiteEnd branches (basis a)
      (mapOnRings i (ShortAffineJacobian318.x (A i) (B i)))=
    mapOnRings i (ShortAffineJacobian318.x (A i) (B i)):=by
  simp only [finite_x,map_mul,map_sub,AlgHom.commutes,
    FourRootCoordinateRingSigns318.finite_base]

/-- Retain the exact original root product and ordinate scale. This
identity holds in the WHOLE source ring, including the ramification locus. -/
lemma signed_y (i:Fin 4) (a:Labels):
    FourRootCoordinateRingSigns318.finiteEnd branches (basis a)
      (mapOnRings i (ShortAffineJacobian318.y (A i) (B i)))=
    algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches)
      (FourBinaryCharacters318.complementary (F:=ℂ) i (basis a))*
        mapOnRings i (ShortAffineJacobian318.y (A i) (B i)):=by
  rw [finite_y]
  simp only [map_mul,AlgHom.commutes,map_prod,FourRootCoordinateRingSigns318.finite_root]
  rw [Finset.prod_mul_distrib,←map_prod,complementary_product]
  ring

lemma toggle_sign (i:Fin 4):
    FourBinaryCharacters318.complementary (F:=ℂ) i (basis (toggle i))= -1:=by
  rw [PELOriginalContactCharacterIdentity318.field_character]
  simp [PELOriginalCharacterQuotient318.toggle]

lemma toggle_y (i:Fin 4):
    FourRootCoordinateRingSigns318.finiteEnd branches (basis (toggle i))
      (mapOnRings i (ShortAffineJacobian318.y (A i) (B i)))=
    -mapOnRings i (ShortAffineJacobian318.y (A i) (B i)):=by
  rw [signed_y,toggle_sign,map_neg,map_one,neg_one_mul]
end PELOriginalFiniteCharacterSigns318
