module
public import FiniteCompletedEqualizer318
public import LiteralSchemeCancellation318
public import LiteralThreeTorsion318
public section
noncomputable section
namespace LiteralFiniteKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
abbrev domain := ShortAffineScheme318.scheme A B
@[expose] def tripling : domain N ⟶ WeierstrassGluing318.literalScheme N :=
  WeierstrassGluing318.finiteChart A B ≫ CompletedIteratedAddition318.tripling A B hD
@[expose] def zero : domain N ⟶ WeierstrassGluing318.literalScheme N :=
  WeierstrassGluing318.finiteChart A B ≫ WeierstrassGluing318.structureMap A B ≫
    WeierstrassGluing318.infinity A B

/-- Literal Scheme-level cancellation is applied to the actual whole finite chart.
The nonverticality needed by the old equalizer is now a proved conclusion. -/
theorem condition_iff {X:Scheme} (f:X ⟶ domain N) :
    f ≫ tripling N=f ≫ zero N ↔
      f ≫ FiniteCompletedEqualizer318.doubling A B hD=
        f ≫ FiniteCompletedEqualizer318.negative A B := by
  simpa only [tripling,zero,FiniteCompletedEqualizer318.doubling,
    FiniteCompletedEqualizer318.negative,Category.assoc] using
    LiteralSchemeCancellation318.tripling_zero_iff N (f ≫ WeierstrassGluing318.finiteChart A B)

lemma condition : ThreeTorsionScheme318.inclusion A B hD ≫ tripling N=
    ThreeTorsionScheme318.inclusion A B hD ≫ zero N :=
  (condition_iff N _).mpr (FiniteCompletedEqualizer318.condition A B hD)

/-- Every Scheme-valued finite point killed by actual completed tripling
factors uniquely through the entire original rank-eight torsion scheme. -/
theorem universal {X:Scheme} (f:X ⟶ domain N) (hf:f ≫ tripling N=f ≫ zero N) :
    ∃!g:X ⟶ ThreeTorsionScheme318.scheme A B hD,
      g ≫ ThreeTorsionScheme318.inclusion A B hD=f :=
  FiniteCompletedEqualizer318.universal A B hD f ((condition_iff N f).mp hf)

@[expose] def fork : Fork (tripling N) (zero N) :=
  Fork.ofι (ThreeTorsionScheme318.inclusion A B hD) (condition N)

/-- Exact categorical equalizer of actual tripling and actual zero on the entire
finite chart. The global completed kernel and zero-section decomposition
remain separate. -/
@[expose] def isLimit : IsLimit (fork N) :=
  Fork.IsLimit.ofExistsUnique (fun s=>universal N s.ι s.condition)
end LiteralFiniteKernel318
