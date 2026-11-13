module
public import ActualTwoDescentOriginalLocalFieldEmbeddingsRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootFractionalModuleRebuild318
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalRootLocalParameter318 ActualTwoDescentOriginalRootNativeDVR318
open ActualTwoDescentOriginalRootIdeals318 ActualTwoDescentAffineChartCoordinates318
open ActualTwoDescentOriginalLocalFieldEmbeddingsRebuild318
universe u
variable {K : Type u} [Field K] [CharZero K]
local instance (n : K) (i : Fin 3) : Algebra (RootLocalRing n i) ((originalCubicScheme n).functionField) := (rootEmbedding n i).toAlgebra

def extendedIdeal (n : K) (i : Fin 3) : Ideal (RootLocalRing n i) :=
  (rootIdeal n i).map (algebraMap (AffineChart n) (RootLocalRing n i))
lemma extendedIdeal_eq (n : K) (hn : n ≠ 0) (i : Fin 3) :
    extendedIdeal n i=Ideal.span {rootLocalY n i} := by
  rw [extendedIdeal,Localization.AtPrime.map_eq_maximalIdeal,
    actual_root_maximal_principal n hn i]

def lattice (n : K) (i : Fin 3) : Submodule (RootLocalRing n i) ((originalCubicScheme n).functionField) :=
  ActualTwoDescentFractionalGeneratorModuleRebuild318.lattice (RootLocalRing n i) ((originalCubicScheme n).functionField)
    (rootEmbedding n i (rootLocalY n i))

def frame (n : K) (i : Fin 3) : RootLocalRing n i ≃ₗ[RootLocalRing n i] lattice n i :=
  ActualTwoDescentFractionalGeneratorModuleRebuild318.frame (RootLocalRing n i) ((originalCubicScheme n).functionField) _
    ((map_ne_zero_iff _ (root_injective n i)).mpr (actual_root_local_y_nonzero n i))
    (root_injective n i)

/-- Full original root ideal image equals yR inside the SAME original
function field, with the actual coefficient embedding fixed. -/
def equivalence (n : K) (hn : n ≠ 0) (i : Fin 3) : extendedIdeal n i ≃ₗ[RootLocalRing n i] lattice n i :=
  (ActualTwoDescentPrincipalIdealModuleFrame318.principalModuleFrame
    (extendedIdeal n i) (rootLocalY n i) (extendedIdeal_eq n hn i)
    (actual_root_local_y_nonzero n i)).symm.trans (frame n i)

lemma value (n : K) (hn : n ≠ 0) (i : Fin 3) (x : extendedIdeal n i) :
    (equivalence n hn i x : (originalCubicScheme n).functionField)=rootEmbedding n i (x : RootLocalRing n i) := by
  let e := ActualTwoDescentPrincipalIdealModuleFrame318.principalModuleFrame
    (extendedIdeal n i) (rootLocalY n i) (extendedIdeal_eq n hn i)
    (actual_root_local_y_nonzero n i)
  have hx := congrArg (fun z : extendedIdeal n i => (z : RootLocalRing n i)) (e.apply_symm_apply x)
  change (e.symm x)*rootLocalY n i=(x : RootLocalRing n i) at hx
  change rootEmbedding n i (e.symm x)*rootEmbedding n i (rootLocalY n i)=_
  rw [←map_mul,hx]

lemma mem_lattice (n : K) (i : Fin 3) (z : (originalCubicScheme n).functionField) : z ∈ lattice n i ↔
    ∃ r : RootLocalRing n i, rootEmbedding n i r*rootEmbedding n i (rootLocalY n i)=z := Iff.rfl
end ActualTwoDescentOriginalRootFractionalModuleRebuild318
