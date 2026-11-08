module
public import LiteralKernelOpenClosed318
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace LiteralKernelComplement318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "ι" => ThreeTorsionTriplingFiber318.toFiber A B hD
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD
local instance finite_open : IsOpenImmersion ι := (LiteralKernelOpenClosed318.canonical_open_closed N).1
local instance finite_closed : IsClosedImmersion ι := (LiteralKernelOpenClosed318.canonical_open_closed N).2

/-- The actual complementary open in the global literal tripling kernel.
This definition does not identify it with the zero section. -/
@[expose] def complementOpen : (K).Opens :=
  ⟨(Set.range ι)ᶜ,(ι).isClosedEmbedding.isClosed_range.isOpen_compl⟩
@[expose] def complement : Scheme := (complementOpen N).toScheme
@[expose] def inclusion : complement N ⟶ K := (complementOpen N).ι
instance inclusion_open : IsOpenImmersion (inclusion N) := by dsimp only [inclusion]; infer_instance

lemma complementary : IsCompl (ι).opensRange (inclusion N).opensRange := by
  change IsCompl (ι).opensRange ((complementOpen N).ι).opensRange
  rw [Scheme.Opens.opensRange_ι]
  constructor
  · rw [disjoint_iff]
    ext x
    simp [complementOpen]
  · rw [codisjoint_iff]
    ext x
    simp [complementOpen]

@[expose] def isColimit : IsColimit (BinaryCofan.mk ι (inclusion N)) :=
  (nonempty_isColimit_binaryCofanMk_of_isCompl ι (inclusion N) (complementary N)).some

/-- Actual coproduct decomposition into the original rank-eight component
and its literal complementary open. Identifying the latter with the base
requires the independent zero-neighborhood theorem. -/
@[expose] def iso : K ≅ ThreeTorsionScheme318.scheme A B hD ⨿ complement N :=
  (isColimit N).coconePointUniqueUpToIso (colimit.isColimit _)
@[reassoc] lemma finite_iso_hom : ι ≫ (iso N).hom=coprod.inl :=
  (isColimit N).comp_coconePointUniqueUpToIso_hom _ ⟨.left⟩
@[reassoc] lemma complement_iso_hom : inclusion N ≫ (iso N).hom=coprod.inr :=
  (isColimit N).comp_coconePointUniqueUpToIso_hom _ ⟨.right⟩
end LiteralKernelComplement318
