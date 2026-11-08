module
public import ThreeTorsionCompletedEqualizer318
public import LiteralSchemeCancellation318
public import LiteralThreeTorsion318
public section
noncomputable section
namespace LiteralNonverticalKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
abbrev domain := Spec (CommRingCat.of (NonverticalDoubling318.OpenRing A B))
@[expose] def tripling : domain N ⟶ WeierstrassGluing318.literalScheme N :=
  NonverticalCompletedDoubling318.intoCompleted A B ≫ CompletedIteratedAddition318.tripling A B hD
@[expose] def zero : domain N ⟶ WeierstrassGluing318.literalScheme N :=
  NonverticalCompletedDoubling318.intoCompleted A B ≫ WeierstrassGluing318.structureMap A B ≫
    WeierstrassGluing318.infinity A B

/-- Literal Scheme-level cancellation is applied to the actual inclusion of
D(2y), so its exact output is the previously checked restricted equalizer. -/
theorem condition_iff {X:Scheme} (f:X ⟶ domain N) :
    f ≫ tripling N=f ≫ zero N ↔
      f ≫ ThreeTorsionCompletedEqualizer318.doubling A B hD=
        f ≫ ThreeTorsionCompletedEqualizer318.negation A B := by
  simpa only [tripling,zero,ThreeTorsionCompletedEqualizer318.doubling,
    ThreeTorsionCompletedEqualizer318.negation,Category.assoc] using
    LiteralSchemeCancellation318.tripling_zero_iff N (f ≫ NonverticalCompletedDoubling318.intoCompleted A B)

lemma condition : ThreeTorsionEqualizerScheme318.inclusion A B hD ≫ tripling N=
    ThreeTorsionEqualizerScheme318.inclusion A B hD ≫ zero N :=
  (condition_iff N _).mpr (ThreeTorsionCompletedEqualizer318.condition A B hD)

/-- Every Scheme-valued nonvertical point killed by actual completed tripling
factors uniquely through the entire original rank-eight torsion scheme. -/
theorem universal {X:Scheme} (f:X ⟶ domain N) (hf:f ≫ tripling N=f ≫ zero N) :
    ∃!g:X ⟶ ThreeTorsionScheme318.scheme A B hD,
      g ≫ ThreeTorsionEqualizerScheme318.inclusion A B hD=f :=
  ThreeTorsionCompletedEqualizer318.universal A B hD f ((condition_iff N f).mp hf)

@[expose] def fork : Fork (tripling N) (zero N) :=
  Fork.ofι (ThreeTorsionEqualizerScheme318.inclusion A B hD) (condition N)

/-- Exact categorical equalizer of actual tripling and actual zero on D(2y).
The whole curve's kernel and the complement of the zero section are not
identified by this restricted statement. -/
@[expose] def isLimit : IsLimit (fork N) :=
  Fork.IsLimit.ofExistsUnique (fun s=>universal N s.ι s.condition)
end LiteralNonverticalKernel318
