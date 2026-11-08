module
public import LiteralKernelFiniteEtale318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace LiteralKernelCoordinateRing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "R" => OpenJModel318.Base N
local notation "T" => ThreeTorsionAlgebra318.Ring A B hD
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD

/-- Actual coordinate algebra of the whole kernel, including its zero
component. The base algebra is the diagonal product algebra. -/
abbrev Ring := T × R
@[expose] def iso : K ≅ Spec (CommRingCat.of (Ring N)) :=
  LiteralFullKernel318.iso N ≪≫ asIso (coprodSpec T R)

lemma coprod_base : coprodSpec T R ≫ Spec.algebraMap R (Ring N)=LiteralKernelFiniteEtale318.coproductMap N := by
  apply coprod.hom_ext
  · rw [←Category.assoc,coprodSpec_inl,←Spec.map_comp]
    rw [LiteralKernelFiniteEtale318.coproductMap,coprod.inl_desc]
    rfl
  · rw [←Category.assoc,coprodSpec_inr,←Spec.map_comp]
    change Spec.map (𝟙 (CommRingCat.of R))=coprod.inr ≫ LiteralKernelFiniteEtale318.coproductMap N
    rw [Spec.map_id,LiteralKernelFiniteEtale318.coproductMap,coprod.inr_desc]
@[reassoc] theorem iso_hom_base : (iso N).hom ≫ Spec.algebraMap R (Ring N)=LiteralKernelFiniteEtale318.structureMap N := by
  rw [iso,Iso.trans_hom,asIso_hom,Category.assoc,coprod_base,LiteralKernelFiniteEtale318.iso_hom_structure]

@[reassoc] theorem finite_projection : ThreeTorsionTriplingFiber318.toFiber A B hD ≫ (iso N).hom=
    Spec.map (CommRingCat.ofHom (RingHom.fst T R)) := by
  simp only [iso,Iso.trans_hom,asIso_hom,←Category.assoc,LiteralFullKernel318.finite_iso_hom]
  exact coprodSpec_inl T R
@[reassoc] theorem zero_projection : LiteralKernelZeroSection318.toKernel N ≫ (iso N).hom=
    Spec.map (CommRingCat.ofHom (RingHom.snd T R)) := by
  simp only [iso,Iso.trans_hom,asIso_hom,←Category.assoc,LiteralFullKernel318.zero_iso_hom]
  exact coprodSpec_inr T R

lemma finite : Module.Finite R (Ring N) := by
  haveI:=ThreeTorsionAlgebra318.finite A B hD
  infer_instance
lemma free : Module.Free R (Ring N) := by
  haveI:=ThreeTorsionAlgebra318.free A B hD
  infer_instance

/-- Numerical rank over a nontrivial literal base. The nontriviality
condition is retained: the N=0 localization may be the zero ring. -/
theorem rank_nine [Nontrivial R] : Module.finrank R (Ring N)=9 := by
  haveI:=ThreeTorsionAlgebra318.finite A B hD
  haveI:=ThreeTorsionAlgebra318.free A B hD
  change Module.finrank R (T × R)=9
  rw [Module.finrank_prod,ThreeTorsionAlgebra318.rank_eight,Module.finrank_self]

theorem rank_nine_of_level_ne_zero [NeZero N] : Module.finrank R (Ring N)=9 := rank_nine N

lemma etale : Algebra.Etale R (Ring N) := by
  haveI:Etale (LiteralKernelFiniteEtale318.structureMap N):=(LiteralKernelFiniteEtale318.finite_etale N).2
  have h:(iso N).inv ≫ LiteralKernelFiniteEtale318.structureMap N=Spec.algebraMap R (Ring N) := by
    rw [←iso_hom_base,←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  haveI:Etale (Spec.algebraMap R (Ring N)):=h ▸ inferInstance
  exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P:=@Etale) (φ:=CommRingCat.ofHom (algebraMap R (Ring N)))).mp inferInstance)
end LiteralKernelCoordinateRing318
