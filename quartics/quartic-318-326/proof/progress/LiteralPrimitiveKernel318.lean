module
public import LiteralKernelPointCover318
public section
noncomputable section
namespace LiteralPrimitiveKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "E" => WeierstrassGluing318.literalScheme N
local notation "T" => ThreeTorsionScheme318.scheme A B hD
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD
local notation "ι" => ThreeTorsionCompletedDoubling318.inclusion A B hD

/-- Fiberwise nonzero means avoiding the zero section at every underlying
point. Mere inequality of two maps is insufficient on disconnected tests. -/
@[expose] def NowhereZero {X:Scheme} (t:X ⟶ E) : Prop :=
  ∀x:X, t x ∉ Set.range (WeierstrassGluing318.infinity A B)

lemma inclusion_nowhereZero : NowhereZero N ι := by
  intro a
  rintro ⟨b,hb⟩
  have hf:WeierstrassGluing318.infinity A B b ∈ Set.range (WeierstrassGluing318.finiteChart A B) := by
    rw [hb]
    exact ⟨ThreeTorsionScheme318.inclusion A B hD a,rfl⟩
  have hz:b ∈ WeierstrassGluing318.infinity A B ⁻¹ᵁ (WeierstrassGluing318.finiteChart A B).opensRange:=hf
  rw [CompletedZeroTripling318.origin_preimage_finite] at hz
  exact hz

lemma lift_range {X:Scheme} (t:X ⟶ E)
    (h:t ≫ CompletedIteratedAddition318.tripling A B hD=
      t ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B)
    (hn:NowhereZero N t) :
    Set.range (pullback.lift t (t ≫ WeierstrassGluing318.structureMap A B) (by simpa only [Category.assoc] using h)) ⊆
      Set.range (ThreeTorsionTriplingFiber318.toFiber A B hD) := by
  rintro _ ⟨x,rfl⟩
  rcases LiteralKernelPointCover318.covers N
    (pullback.lift t (t ≫ WeierstrassGluing318.structureMap A B) (by simpa only [Category.assoc] using h) x) with hf|hz
  · exact hf
  · obtain ⟨b,hb⟩:=hz
    apply False.elim
    apply hn x
    refine ⟨b,?_⟩
    have he:=congrArg (pullback.fst (CompletedIteratedAddition318.tripling A B hD)
      (WeierstrassGluing318.infinity A B)) hb
    change (LiteralKernelZeroSection318.toKernel N ≫ pullback.fst _ _) b=
      (pullback.lift t (t ≫ WeierstrassGluing318.structureMap A B)
        (by simpa only [Category.assoc] using h) ≫ pullback.fst _ _) x at he
    simpa only [LiteralKernelZeroSection318.toKernel_fst,pullback.lift_fst] using he

/-- The original rank-eight torsion scheme represents actual nowhere-zero
points killed by completed tripling, for arbitrary Scheme tests. -/
theorem universal {X:Scheme} (t:X ⟶ E)
    (h:t ≫ CompletedIteratedAddition318.tripling A B hD=
      t ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B)
    (hn:NowhereZero N t) : ∃!g:X ⟶ T, g ≫ ι=t := by
  haveI:IsOpenImmersion (ThreeTorsionTriplingFiber318.toFiber A B hD):=
    (LiteralKernelOpenClosed318.canonical_open_closed N).1
  let k:X ⟶ K:=pullback.lift t (t ≫ WeierstrassGluing318.structureMap A B)
    (by simpa only [Category.assoc] using h)
  let g:=IsOpenImmersion.lift (ThreeTorsionTriplingFiber318.toFiber A B hD) k (lift_range N t h hn)
  have hg:g ≫ ThreeTorsionTriplingFiber318.toFiber A B hD=k:=IsOpenImmersion.lift_fac _ _ _
  have hgt:g ≫ ι=t := by
    have he:=congrArg (fun f=>f ≫ pullback.fst (CompletedIteratedAddition318.tripling A B hD)
      (WeierstrassGluing318.infinity A B)) hg
    simpa only [Category.assoc,ThreeTorsionTriplingFiber318.toFiber_fst,k,pullback.lift_fst] using he
  refine ⟨g,hgt,?_⟩
  intro g' hg'
  haveI:=ThreeTorsionCompletedClosed318.inclusion_closed A B hD
  exact (cancel_mono ι).mp (hg'.trans hgt.symm)

/-- Exact representability criterion; no field, affine, connected or
reduced hypothesis is placed on the test scheme. -/
theorem exists_iff {X:Scheme} (t:X ⟶ E) :
    (∃g:X ⟶ T,g ≫ ι=t) ↔
      (t ≫ CompletedIteratedAddition318.tripling A B hD=
        t ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B) ∧ NowhereZero N t := by
  constructor
  · rintro ⟨g,rfl⟩
    constructor
    · simp only [Category.assoc,ThreeTorsionCompletedTripling318.inclusion_tripling,
        ThreeTorsionCompletedDoubling318.inclusion_over_base_assoc]
    · intro x
      exact inclusion_nowhereZero N (g x)
  · rintro ⟨h,hn⟩
    exact (universal N t h hn).exists
end LiteralPrimitiveKernel318
