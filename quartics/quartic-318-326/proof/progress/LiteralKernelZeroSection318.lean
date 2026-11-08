module
public import CompletedZeroTripling318
public import LiteralKernelComplement318
public import LiteralKernelFiniteRange318
public section
noncomputable section
namespace LiteralKernelZeroSection318
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

@[expose] def toKernel : Base ⟶ K :=
  pullback.lift (WeierstrassGluing318.infinity A B) (𝟙 _)
    (by rw [CompletedZeroTripling318.tripling_origin,Category.id_comp])
@[reassoc] lemma toKernel_fst : toKernel N ≫ pullback.fst _ _=WeierstrassGluing318.infinity A B := by
  simp only [toKernel,pullback.lift_fst]
@[reassoc] lemma toKernel_snd : toKernel N ≫ pullback.snd _ _=𝟙 _ := by
  simp only [toKernel,pullback.lift_snd]

/-- The actual zero section lands in the genuine complement of the actual
rank-eight component, by its exact finite-chart image formula. -/
lemma range_complement : Set.range (toKernel N) ⊆ Set.range (LiteralKernelComplement318.inclusion N) := by
  change Set.range (toKernel N) ⊆ Set.range ((LiteralKernelComplement318.complementOpen N).ι)
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x,rfl⟩
  change toKernel N x ∉ Set.range (ThreeTorsionTriplingFiber318.toFiber A B hD)
  rw [LiteralKernelFiniteRange318.canonical_range]
  intro hx
  have hh:(toKernel N ≫ pullback.fst (CompletedIteratedAddition318.tripling A B hD)
      (WeierstrassGluing318.infinity A B)) x ∈ Set.range (WeierstrassGluing318.finiteChart A B):=hx
  rw [toKernel_fst] at hh
  have he:x ∈ WeierstrassGluing318.infinity A B ⁻¹ᵁ (WeierstrassGluing318.finiteChart A B).opensRange:=hh
  rw [CompletedZeroTripling318.origin_preimage_finite] at he
  exact he

@[expose] def intoComplement : Base ⟶ LiteralKernelComplement318.complement N :=
  IsOpenImmersion.lift (LiteralKernelComplement318.inclusion N) (toKernel N) (range_complement N)
@[reassoc] lemma intoComplement_inclusion : intoComplement N ≫ LiteralKernelComplement318.inclusion N=toKernel N :=
  IsOpenImmersion.lift_fac _ _ _
@[expose] def complementStructure : LiteralKernelComplement318.complement N ⟶ Base :=
  LiteralKernelComplement318.inclusion N ≫ pullback.snd
    (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)
@[reassoc] theorem section_retraction : intoComplement N ≫ complementStructure N=𝟙 _ := by
  rw [complementStructure,←Category.assoc,intoComplement_inclusion,toKernel_snd]

/-- A precise remaining interface: once the actual complement projection is
proved to be the actual zero map, its inverse to the base is already fixed.
The hypothesis is explicit and is not asserted by this constructor. -/
@[expose] def complementIsoOfZero
    (hzero:LiteralKernelComplement318.inclusion N ≫
      pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)=
      complementStructure N ≫ WeierstrassGluing318.infinity A B) :
    LiteralKernelComplement318.complement N ≅ Base where
  hom := complementStructure N
  inv := intoComplement N
  hom_inv_id := by
    apply (cancel_mono (LiteralKernelComplement318.inclusion N)).mp
    rw [Category.assoc,intoComplement_inclusion,Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc,toKernel_fst,hzero]
    · rw [Category.assoc,toKernel_snd,Category.comp_id]
      rfl
  inv_hom_id := section_retraction N
end LiteralKernelZeroSection318
