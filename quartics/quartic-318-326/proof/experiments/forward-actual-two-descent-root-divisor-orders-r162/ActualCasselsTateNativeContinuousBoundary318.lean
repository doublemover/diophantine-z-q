module
public import ActualCasselsTateNativeContinuousCoordinates318
public section
noncomputable section
namespace ActualCasselsTateNativeContinuousBoundary318
open TopRep ActualCasselsTateNativeContinuousFaces318
open ActualCasselsTateNativeContinuousCoordinates318
variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (X : TopRep k G)
variable (hact : Continuous (fun p : G × X => X.ρ p.1 p.2))
local notation "N2" => (homogeneousCochains X).X 2
local notation "N3" => (homogeneousCochains X).X 3

include hact in
/-- Literal image criterion for THIS native degree-three cochain, not an
arbitrary abstract isomorphism and not a claim that every cocycle is exact. -/
theorem native_boundary_iff (w : N3) :
    (∃ z : N2, ((homogeneousCochains X).d 2 3).hom z = w) ↔
    ∃ b : C(G × G,X), ∀ g h l : G,
      X.ρ g (b (h,l)) - b (g*h,l) + b (g,h*l) - b (g,h) = (nativeThreeMap X w) (g,h,l) := by
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨nativeTwoMap X z,?_⟩
    intro g h l
    change X.ρ g (evalTwo X z h l) - evalTwo X z (g*h) l + evalTwo X z g (h*l) -
      evalTwo X z g h = evalThree X w g h l
    rw [← eval_native_dTwo,hz]
  · rintro ⟨b,hb⟩
    let z : N2 := fromTwoMap X hact b
    have hz : nativeTwoMap X z = b := eval_fromTwo X hact b
    have hw : nativeThreeMap X (((homogeneousCochains X).d 2 3).hom z) =
        nativeThreeMap X w := by
      apply ContinuousMap.ext
      rintro ⟨g,h,l⟩
      change evalThree X (((homogeneousCochains X).d 2 3).hom z) g h l = _
      rw [eval_native_dTwo]
      change X.ρ g ((nativeTwoMap X z) (h,l)) - (nativeTwoMap X z) (g*h,l) +
        (nativeTwoMap X z) (g,h*l) - (nativeTwoMap X z) (g,h) = _
      rw [hz]
      exact hb g h l
    refine ⟨z,?_⟩
    simpa only [from_evalThree] using congrArg (fromThreeMap X hact) hw
end ActualCasselsTateNativeContinuousBoundary318
