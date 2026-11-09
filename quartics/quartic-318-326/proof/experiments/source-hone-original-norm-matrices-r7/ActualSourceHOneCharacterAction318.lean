module
public import ActualSourceHOneRationalSpanning318
public import SourceHOneCharacterRepresentatives318
public import InfinityReciprocalAction318
public import Mathlib.Tactic.Linarith

public section
noncomputable section
namespace ActualSourceHOneCharacterAction318
attribute [-instance] DivisionRing.toRatAlgebra
open ActualSourceHOnePrincipalRepresentatives318 ActualSourceHOneRationalSpanning318
open SourceHOneCharacterIndices318 SourceHOneCharacterRepresentatives318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance originalField : Field (InfinityFieldCoordinates318.L units) :=
  (KummerTensorField318.source_raw_field units).toField

@[expose] def infinitySign (b : Fin 4 → Bool) :=
  InfinityReciprocalAction318.restrict units
    (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b)

/-- The actual whole infinity ring is preserved by the same overlap sign map. -/
theorem infinity_sign_square (b : Fin 4 → Bool) (x : InfinityOpenChart318.OpenOrder units) :
    InfinityOverlapLocalization318.toOpen units (infinitySign b x) =
      ContactGlobalSigns318.openEquiv units b (InfinityOverlapLocalization318.toOpen units x) := by
  apply SourceOpenFractionField318.openEmbedding_injective units
  rw [InfinityOverlapLocalization318.toOpen_embedding,
    SourceSignFieldComparison318.open_embedding,InfinityOverlapLocalization318.toOpen_embedding]
  exact InfinityReciprocalAction318.embedding_square units _ x

/-- Both original chart images, with their original difference sign, are
preserved by the actual overlap automorphism. -/
theorem boundary_kernel_preserved (b : Fin 4 → Bool)
    (x : ActualSourceHOneCoordinates318.OverlapRing) (hx : boundary x = 0) :
    boundary (ContactGlobalSigns318.openEquiv units b x) = 0 := by
  obtain ⟨a,d,had⟩ := (ActualSourceHOneCoordinates318.boundary_eq_zero_iff x).mp hx
  change SourceOpenFractionField318.orderToOpen units a -
    InfinityOverlapLocalization318.toOpen units d = x at had
  apply (ActualSourceHOneCoordinates318.boundary_eq_zero_iff _).mpr
  refine ⟨SourceSignFieldComparison318.sourceEquiv units b a,infinitySign b d,?_⟩
  change SourceOpenFractionField318.orderToOpen units _ - InfinityOverlapLocalization318.toOpen units _ = _
  rw [SourceSignFieldComparison318.order_to_open,infinity_sign_square,← map_sub]
  exact congrArg (ContactGlobalSigns318.openEquiv units b) had

@[expose] def signedBoundary (b : Fin 4 → Bool) :
    ActualSourceHOneCoordinates318.OverlapRing →ₗ[ℚ] HOne :=
  boundaryLinear.comp (ContactGlobalSigns318.openEquiv units b).toAddEquiv.toAddMonoidHom.toRatLinearMap

theorem kernel_le_signed (b : Fin 4 → Bool) : boundaryLinear.ker ≤ (signedBoundary b).ker := by
  intro x hx
  exact boundary_kernel_preserved b x hx

/-- The original overlap sign descends to the actual source H1 quotient.
Agreement with a separately constructed sheaf pullback action is not assumed. -/
@[expose] def action (b : Fin 4 → Bool) : HOne →ₗ[ℚ] HOne :=
  boundaryLinear.liftOfSurjective ActualSourceHOneCoordinates318.boundary_surjective
    ⟨signedBoundary b,kernel_le_signed b⟩

theorem action_boundary (b : Fin 4 → Bool) (x : ActualSourceHOneCoordinates318.OverlapRing) :
    action b (boundary x) = boundary (ContactGlobalSigns318.openEquiv units b x) := by
  change (boundaryLinear.liftOfSurjective _)
    ⟨signedBoundary b,kernel_le_signed b⟩ (boundaryLinear x) = _
  rw [LinearMap.equivOfSurjective_apply] <;> rfl

theorem action_twice (b : Fin 4 → Bool) (y : HOne) : action b (action b y) = y := by
  obtain ⟨x,rfl⟩ := ActualSourceHOneCoordinates318.boundary_surjective y
  rw [action_boundary,action_boundary]
  have h : ContactGlobalSigns318.openEquiv units b (ContactGlobalSigns318.openEquiv units b x) = x :=
    congrArg (fun e : ContactKummerOrder318.OpenOrder units ≃ₐ[ContactKummerOrder318.OpenBase]
      ContactKummerOrder318.OpenOrder units => e x)
      (FourRootOrderSigns318.signEquiv_trans_self _ b)
  rw [h]

/-- The explicit whole-source H1 coordinate with the original root character. -/
@[expose] def characterClass (i : Index) : HOne := boundary (representative units i)

/-- Actual eigencharacter statement on the unchanged source H1, obtained by
ring compatibility and the genuine quotient kernel rather than assumed. -/
theorem action_characterClass (i : Index) (b : Fin 4 → Bool) :
    action b (characterClass i) = epsilon i b • characterClass i := by
  rw [characterClass,action_boundary,representative_sign]
  have hfactor : (epsilon i b - 1) * (epsilon i b + 1) = 0 := by
    nlinarith [epsilon_square i b]
  rcases mul_eq_zero.mp hfactor with hp | hm
  · have he : epsilon i b = 1 := by linarith
    simp only [he, map_one, one_mul, one_smul]
  · have he : epsilon i b = -1 := by linarith
    simp only [he, map_neg, map_one, neg_one_mul, neg_one_smul]

end ActualSourceHOneCharacterAction318
