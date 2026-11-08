module
public import LiteralFullKernel318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace LiteralKernelFiniteEtale318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "Base" => Spec (CommRingCat.of (OpenJModel318.Base N))
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD
local notation "T" => ThreeTorsionScheme318.scheme A B hD

@[expose] def structureMap : K ⟶ Base := pullback.snd _ _
@[expose] def coproductMap : T ⨿ Base ⟶ Base :=
  coprod.desc (ThreeTorsionScheme318.structureMap A B hD) (𝟙 _)

@[reassoc] theorem iso_inv_structure : (LiteralFullKernel318.iso N).inv ≫ structureMap N=coproductMap N := by
  apply coprod.hom_ext
  · simp only [←Category.assoc,LiteralFullKernel318.inl_iso_inv,structureMap,
      ThreeTorsionTriplingFiber318.toFiber_snd,coproductMap,coprod.inl_desc]
  · simp only [←Category.assoc,LiteralFullKernel318.inr_iso_inv,structureMap,
      LiteralKernelZeroSection318.toKernel_snd,coproductMap,coprod.inr_desc]
@[reassoc] theorem iso_hom_structure : (LiteralFullKernel318.iso N).hom ≫ coproductMap N=structureMap N := by
  rw [←iso_inv_structure,←Category.assoc,Iso.hom_inv_id,Category.id_comp]

lemma coproduct_finite : IsFinite (coproductMap N) := by
  haveI: IsFinite (ThreeTorsionScheme318.structureMap A B hD):=(ThreeTorsionScheme318.finite_etale A B hD).1
  dsimp only [coproductMap]
  infer_instance
lemma coproduct_etale : Etale (coproductMap N) := by
  apply IsZariskiLocalAtSource.of_openCover (P:=@Etale) (coprodOpenCover.{0,0} T Base)
  intro i
  rcases i with i|i
  · change Etale (coprod.inl ≫ coproductMap N)
    rw [coproductMap,coprod.inl_desc]
    exact (ThreeTorsionScheme318.finite_etale A B hD).2
  · change Etale (coprod.inr ≫ coproductMap N)
    rw [coproductMap,coprod.inr_desc]
    infer_instance

/-- The actual entire literal tripling fiber is finite and etale over the
original base, by its exact coproduct decomposition over that base. -/
theorem finite_etale : IsFinite (structureMap N) ∧ Etale (structureMap N) := by
  rw [←iso_hom_structure N]
  haveI:=coproduct_finite N
  haveI:=coproduct_etale N
  exact ⟨inferInstance,inferInstance⟩
end LiteralKernelFiniteEtale318
