module
public import LiteralTriplingHom318
public section
noncomputable section
namespace LiteralTriplingAdditive318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralSchemePointOperations318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "pE" => WeierstrassGluing318.structureMap A B
local notation "t" => CompletedIteratedAddition318.tripling A B hD
@[expose] def pairMap : pullback pE pE ⟶ pullback pE pE:=
  pullback.lift (pullback.fst _ _ ≫ t) (pullback.snd _ _ ≫ t) (by
    simp only [Category.assoc,CompletedIteratedAddition318.tripling_over_base,pullback.condition])
@[reassoc] theorem pairMap_fst : pairMap N ≫ pullback.fst _ _=pullback.fst pE pE ≫ t:=by simp [pairMap]
@[reassoc] theorem pairMap_snd : pairMap N ≫ pullback.snd _ _=pullback.snd pE pE ≫ t:=by simp [pairMap]

/-- Actual multiplication compatibility for the tripling endomorphism of
the completed literal family, proved on the universal pair Scheme. -/
theorem additive : CompletedAddition318.addition A B hD ≫ t=
    pairMap N ≫ CompletedAddition318.addition A B hD:=by
  let b:=pullback.fst pE pE ≫ pE
  let p:Points N b:=⟨pullback.fst _ _,rfl⟩
  let q:Points N b:=⟨pullback.snd _ _,pullback.condition.symm⟩
  have hpq:pair N b p q=𝟙 (pullback pE pE):=by
    apply pullback.hom_ext
    · rw [pair_fst,Category.id_comp]
    · rw [pair_snd,Category.id_comp]
  have ht:pair N b (3 • p) (3 • q)=pairMap N:=by
    apply pullback.hom_ext
    · rw [pair_fst,pairMap_fst,LiteralTriplingHom318.three_value]
    · rw [pair_snd,pairMap_snd,LiteralTriplingHom318.three_value]
  have h:=congrArg Subtype.val (nsmul_add p q 3)
  rw [LiteralTriplingHom318.three_value] at h
  change (pair N b p q ≫ CompletedAddition318.addition A B hD) ≫ t=
    pair N b (3 • p) (3 • q) ≫ CompletedAddition318.addition A B hD at h
  rwa [hpq,ht,Category.id_comp] at h
end LiteralTriplingAdditive318
