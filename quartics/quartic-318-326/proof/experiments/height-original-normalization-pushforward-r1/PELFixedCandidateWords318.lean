module
public import PELDirichletSidePairingData318
public import PELOriginalPrimeBaseInvolutions318
public section
noncomputable section
namespace PELFixedCandidateWords318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELNormOneBaseAction318 PELOriginalPrimeBaseInvolutions318
set_option maxHeartbeats 2400000
/-- Original generators: all28 original integral side units, then the four
specified positive prime normalizers. No new normalizer is postulated. -/
@[expose] def generator (j : Fin 32) : positiveNormalizer :=
  if h : j.val<28 then originalNormalizer (PELDirichletSidePairingData318.edgeUnit ⟨j.val,h⟩)
  else originalPrime ⟨j.val-28,by omega⟩
@[expose] def generatorCoordinates (j : Fin 32) : Coordinates :=
  if h : j.val<28 then PELDirichletSidePairingData318.coefficients ⟨j.val,h⟩
  else PELPrimeNormalizerData318.coefficients ⟨j.val-28,by omega⟩

theorem generator_value (j : Fin 32) :
    ((generator j).val:B)=embed (generatorCoordinates j) := by
  fin_cases j <;> rfl

/-- Lists are chronological: each successive generator acts on the LEFT. -/
@[expose] def positiveWord : List (Fin 32) → positiveNormalizer
  | [] => 1
  | j::w => positiveWord w*generator j
@[expose] def integerWord : List (Fin 32) → Coordinates
  | [] => ![1,0,0,0]
  | j::w => product (integerWord w) (generatorCoordinates j)

theorem positiveWord_value (w : List (Fin 32)) :
    ((positiveWord w).val:B)=embed (integerWord w) := by
  induction w with
  | nil =>
    change (1:B)=embed ![1,0,0,0]
    ext <;> norm_num [embed]
  | cons j w ih =>
    change ((positiveWord w).val:B)*((generator j).val:B)=
      embed (product (integerWord w) (generatorCoordinates j))
    rw [ih,generator_value,embed_mul]
end PELFixedCandidateWords318
