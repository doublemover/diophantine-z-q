module
public import IntegralOverlapTensorCompatibility318
public section
noncomputable section
namespace IntegralOverlapSheafCompatibility318
open AlgebraicGeometry CategoryTheory Opposite
open IntegralOverlapChartMaps318 IntegralOverlapCoefficientRestrictions318
open IntegralOverlapCoefficients318 IntegralOverlapTensorCompatibility318
open IntrinsicTensorChartSections318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)

local instance overlapCommRing : CommRing (Overlap R c) := inferInstance
local instance finiteCommRing : CommRing (IntegralBranchCoordinates318.B R c 0) := inferInstance
local instance infinityCommRing : CommRing (IntegralInfinityChart318.Order R c) := inferInstance

variable {Y : Scheme.{u}} (j : Spec (CommRingCat.of (Overlap R c)) ⟶ Y) [IsOpenImmersion j]
  (p : Y ⟶ Spec (CommRingCat.of R))
  (h : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R (Overlap R c))))

/-- Both actual chart expressions coincide in the same ambient intrinsic
cotangent-square sheaf on the whole specified overlap, not only generically. -/
theorem section0_agreement :
    weightedSquare j p h
      (finiteMap R c ((VerticalSection318.J : IntegralBranchCoordinates318.B R c 0)^2 *
        IntegralBranchBicanonical318.coefficient0 R c 0)) (finiteDifferential R c) =
    weightedSquare j p h
      (infinityMap R c ((VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
        IntegralInfinityCoefficients318.coefficient0 R c)) (infinityDifferential R c) := by
  rw [differential_transition,weightedSquare_smul]
  congr 1
  have hJf : finiteMap R c ((VerticalSection318.J:IntegralBranchCoordinates318.B R c 0)^2)=
      (VerticalSection318.J:Overlap R c)^2 := map_weight (finiteMap R c).toRingHom
  have hJi : infinityMap R c ((VerticalSection318.J:IntegralInfinityChart318.Order R c)^2)=
      (VerticalSection318.J:Overlap R c)^2 := map_weight (infinityMap R c).toRingHom
  have hc : commonMap R c (finite0 R c) * (commonMap R c (derivativeFactor R c))^2=
      commonMap R c (infinity0 R c) := by
    have ht := congrArg (commonMap R c).toRingHom (coefficient0_transition R c)
    rw [map_mul,map_pow] at ht
    change commonMap R c (finite0 R c) *
      (commonMap R c (derivativeFactor R c))^2=commonMap R c (infinity0 R c) at ht
    exact ht
  simp only [map_mul,hJf,hJi,finite_coefficient0,infinity_coefficient0]
  change (VerticalSection318.J:Overlap R c)^2 * commonMap R c (finite0 R c) *
      (commonMap R c (derivativeFactor R c))^2 =
    (VerticalSection318.J:Overlap R c)^2 * commonMap R c (infinity0 R c)
  calc
    _ = (VerticalSection318.J:Overlap R c)^2 *
        (commonMap R c (finite0 R c) * (commonMap R c (derivativeFactor R c))^2) :=
      mul_assoc _ _ _
    _ = _ := congrArg (fun z : Overlap R c => (VerticalSection318.J:Overlap R c)^2*z) hc

theorem section1_agreement :
    weightedSquare j p h
      (finiteMap R c ((VerticalSection318.J : IntegralBranchCoordinates318.B R c 0)^2 *
        IntegralBranchBicanonical318.coefficient1 R c 0)) (finiteDifferential R c) =
    weightedSquare j p h
      (infinityMap R c ((VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
        IntegralInfinityCoefficients318.coefficient1 R c)) (infinityDifferential R c) := by
  rw [differential_transition,weightedSquare_smul]
  congr 1
  have hJf : finiteMap R c ((VerticalSection318.J:IntegralBranchCoordinates318.B R c 0)^2)=
      (VerticalSection318.J:Overlap R c)^2 := map_weight (finiteMap R c).toRingHom
  have hJi : infinityMap R c ((VerticalSection318.J:IntegralInfinityChart318.Order R c)^2)=
      (VerticalSection318.J:Overlap R c)^2 := map_weight (infinityMap R c).toRingHom
  have hc : commonMap R c (finite1 R c) * (commonMap R c (derivativeFactor R c))^2=
      commonMap R c (infinity1 R c) := by
    have ht := congrArg (commonMap R c).toRingHom (coefficient1_transition R c)
    rw [map_mul,map_pow] at ht
    change commonMap R c (finite1 R c) *
      (commonMap R c (derivativeFactor R c))^2=commonMap R c (infinity1 R c) at ht
    exact ht
  simp only [map_mul,hJf,hJi,finite_coefficient1,infinity_coefficient1]
  change (VerticalSection318.J:Overlap R c)^2 * commonMap R c (finite1 R c) *
      (commonMap R c (derivativeFactor R c))^2 =
    (VerticalSection318.J:Overlap R c)^2 * commonMap R c (infinity1 R c)
  calc
    _ = (VerticalSection318.J:Overlap R c)^2 *
        (commonMap R c (finite1 R c) * (commonMap R c (derivativeFactor R c))^2) :=
      mul_assoc _ _ _
    _ = _ := congrArg (fun z : Overlap R c => (VerticalSection318.J:Overlap R c)^2*z) hc

variable (jF : Spec (CommRingCat.of (IntegralBranchCoordinates318.B R c 0)) ⟶ Y)
  (jI : Spec (CommRingCat.of (IntegralInfinityChart318.Order R c)) ⟶ Y)
  [IsOpenImmersion jF] [IsOpenImmersion jI]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom (show IntegralBranchCoordinates318.B R c 0 →+* Overlap R c from (finiteMap R c).toRingHom)))]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom (show IntegralInfinityChart318.Order R c →+* Overlap R c from (infinityMap R c).toRingHom)))]
  (hF : jF ≫ p=Spec.map (CommRingCat.ofHom
    (algebraMap R (IntegralBranchCoordinates318.B R c 0))))
  (hI : jI ≫ p=Spec.map (CommRingCat.ofHom
    (algebraMap R (IntegralInfinityChart318.Order R c))))
  (routeF : Spec.map (CommRingCat.ofHom (show IntegralBranchCoordinates318.B R c 0 →+* Overlap R c from (finiteMap R c).toRingHom)) ≫ jF=j)
  (routeI : Spec.map (CommRingCat.ofHom (show IntegralInfinityChart318.Order R c →+* Overlap R c from (infinityMap R c).toRingHom)) ≫ jI=j)
  (leF : j ''ᵁ ⊤ ≤ jF ''ᵁ ⊤) (leI : j ''ᵁ ⊤ ≤ jI ''ᵁ ⊤)

include h routeF routeI in
/-- Exact naturality identifies restrictions of the two original J²-weighted
chart sections with the expressions compared above. Scheme construction and
full intersection coverage are deliberately not premises disguised as conclusions. -/
theorem restrictions0_agree :
    (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE leF).op
      (weightedSquare jF p hF
        ((VerticalSection318.J : IntegralBranchCoordinates318.B R c 0)^2 *
          IntegralBranchBicanonical318.coefficient0 R c 0)
        (KaehlerDifferential.D R (IntegralBranchCoordinates318.B R c 0)
          (IntegralBranchCoordinates318.sourceCoordinate R c 0))) =
    (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE leI).op
      (weightedSquare jI p hI
        ((VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
          IntegralInfinityCoefficients318.coefficient0 R c)
        (KaehlerDifferential.D R (IntegralInfinityChart318.Order R c)
          (IntegralInfinityChart318.coordinate R c))) := by
  rw [weightedSquare_restrict_to jF p hF (finiteMap R c) j h routeF leF,
    weightedSquare_restrict_to jI p hI (infinityMap R c) j h routeI leI]
  exact section0_agreement R c j p h

include h routeF routeI in
theorem restrictions1_agree :
    (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE leF).op
      (weightedSquare jF p hF
        ((VerticalSection318.J : IntegralBranchCoordinates318.B R c 0)^2 *
          IntegralBranchBicanonical318.coefficient1 R c 0)
        (KaehlerDifferential.D R (IntegralBranchCoordinates318.B R c 0)
          (IntegralBranchCoordinates318.sourceCoordinate R c 0))) =
    (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE leI).op
      (weightedSquare jI p hI
        ((VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
          IntegralInfinityCoefficients318.coefficient1 R c)
        (KaehlerDifferential.D R (IntegralInfinityChart318.Order R c)
          (IntegralInfinityChart318.coordinate R c))) := by
  rw [weightedSquare_restrict_to jF p hF (finiteMap R c) j h routeF leF,
    weightedSquare_restrict_to jI p hI (infinityMap R c) j h routeI leI]
  exact section1_agreement R c j p h
end IntegralOverlapSheafCompatibility318
