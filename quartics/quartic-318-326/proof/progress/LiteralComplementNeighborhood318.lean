module
public import InfinityOriginNeighborhood318
public import LiteralKernelZeroSection318
public section
noncomputable section
namespace LiteralComplementNeighborhood318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N

@[expose] def point : LiteralKernelComplement318.complement N ⟶ WeierstrassGluing318.literalScheme N :=
  LiteralKernelComplement318.inclusion N ≫ pullback.fst
    (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)
lemma global_base :
    pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B) ≫
      WeierstrassGluing318.structureMap A B=pullback.snd _ _ := by
  have h:=congrArg (fun k=>k ≫ WeierstrassGluing318.structureMap A B)
    (pullback.condition (f:=CompletedIteratedAddition318.tripling A B hD) (g:=WeierstrassGluing318.infinity A B))
  simpa only [Category.assoc,CompletedIteratedAddition318.tripling_over_base,
    WeierstrassGluing318.infinity_section,Category.comp_id] using h
@[reassoc] lemma point_base : point N ≫ WeierstrassGluing318.structureMap A B=
    LiteralKernelZeroSection318.complementStructure N := by
  rw [point,Category.assoc,global_base]
  rfl
lemma point_tripling_zero : point N ≫ CompletedIteratedAddition318.tripling A B hD=
    point N ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  simp only [point,Category.assoc,pullback.condition]
  rw [←global_base N]
  simp only [Category.assoc]
lemma point_double_neg : point N ≫ CompletedIteratedAddition318.doubling A B hD=
    point N ≫ GluedNegation318.negation A B :=
  (LiteralSchemeCancellation318.tripling_zero_iff N (point N)).mp (point_tripling_zero N)

lemma range_neighborhood (d:InfinityChart318.Ring A B) (hd:IsUnit (InfinityChart318.origin A B d)) :
    Set.range (point N) ⊆ Set.range (InfinityOriginNeighborhood318.intoCurve A B d) := by
  rintro _ ⟨x,rfl⟩
  rcases InfinityOriginNeighborhood318.covers A B d hd (point N x) with hf|hn
  · have hx:LiteralKernelComplement318.inclusion N x ∉
        Set.range (ThreeTorsionTriplingFiber318.toFiber A B hD):=x.property
    apply False.elim
    apply hx
    rw [LiteralKernelFiniteRange318.canonical_range]
    exact hf
  · exact hn

/-- The whole actual complementary kernel scheme uniquely lifts into every
actual infinity neighborhood whose origin denominator is a unit. -/
@[expose] def lift (d:InfinityChart318.Ring A B) (hd:IsUnit (InfinityChart318.origin A B d)) :
    LiteralKernelComplement318.complement N ⟶ InfinityOriginNeighborhood318.neighborhood A B d :=
  IsOpenImmersion.lift (InfinityOriginNeighborhood318.intoCurve A B d) (point N) (range_neighborhood N d hd)
@[reassoc] lemma lift_intoCurve (d:InfinityChart318.Ring A B) (hd:IsUnit (InfinityChart318.origin A B d)) :
    lift N d hd ≫ InfinityOriginNeighborhood318.intoCurve A B d=point N := IsOpenImmersion.lift_fac _ _ _

/-- Exact remaining join: an actual all-Scheme zero-neighborhood theorem
forces the genuine complementary kernel component to be the actual zero
section. The neighborhood hypothesis remains explicit here. -/
theorem complement_zero_of_neighborhood
    (d:InfinityChart318.Ring A B) (hd:IsUnit (InfinityChart318.origin A B d))
    (hlocal:∀ {X:Scheme} (x:X ⟶ InfinityOriginNeighborhood318.neighborhood A B d),
      x ≫ InfinityOriginNeighborhood318.intoCurve A B d ≫ CompletedIteratedAddition318.doubling A B hD=
        x ≫ InfinityOriginNeighborhood318.intoCurve A B d ≫ GluedNegation318.negation A B →
      x ≫ InfinityOriginNeighborhood318.intoCurve A B d=
        x ≫ InfinityOriginNeighborhood318.intoCurve A B d ≫ WeierstrassGluing318.structureMap A B ≫
          WeierstrassGluing318.infinity A B) :
    point N=LiteralKernelZeroSection318.complementStructure N ≫ WeierstrassGluing318.infinity A B := by
  have hh:=hlocal (lift N d hd) (by
    simpa only [←Category.assoc,lift_intoCurve] using point_double_neg N)
  simpa only [←Category.assoc,lift_intoCurve,point_base] using hh
end LiteralComplementNeighborhood318
