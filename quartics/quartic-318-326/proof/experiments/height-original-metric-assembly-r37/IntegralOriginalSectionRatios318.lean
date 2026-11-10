module
public import IntegralGeneratedTensorSheaf318
public section
noncomputable section
namespace IntegralOriginalSectionRatios318
open AlgebraicGeometry CategoryTheory
open IntegralGluedModel318 IntegralGluedDifferentialFrames318 IntegralGlobalBicanonicalPair318
open IntrinsicTensorChartSections318
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

@[expose] def branchRatio (i : Fin 4) : Γ(scheme R c,opens R c (some i)) :=
  ((branchEmbedding R c i).appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of (IntegralBranchCoordinates318.B R c i))).inv
      (IntegralBranchCoordinates318.sourceT R c i))
@[expose] def infinityRatio : Γ(scheme R c,opens R c none) :=
  ((infinityChart R c).appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of (IntegralInfinityChart318.Order R c))).inv
      (IntegralInfinityCoefficients318.k0 R c * IntegralInfinityChart318.coordinate R c ^ 2))

theorem branch_coefficients (i : Fin 4) : branchCoefficient R c i 1=
    IntegralBranchCoordinates318.sourceT R c i * branchCoefficient R c i 0 := by
  simp only [branchCoefficient,show (1:Fin 2)≠0 by decide,ite_false,ite_true,
    IntegralBranchBicanonical318.coefficient1]
  ring

theorem infinity_coefficients : infinityCoefficient R c 0=
    (IntegralInfinityCoefficients318.k0 R c * IntegralInfinityChart318.coordinate R c ^ 2) *
      infinityCoefficient R c 1 := by
  simp only [infinityCoefficient,show (1:Fin 2)≠0 by decide,ite_false,ite_true,
    IntegralInfinityCoefficients318.coefficient0_relation]
  ring

/-- The literal finite ratio is the ORIGINAL t, not the y0 coordinate of
the auxiliary finite projective projection. -/
theorem branch_relation (i : Fin 4) :
    branchQ R c i 1=branchRatio R c i • branchQ R c i 0 := by
  unfold branchQ branchRatio
  rw [branch_coefficients]
  exact weightedSquare_mul _ _ _ _ _ _

/-- The reciprocal ratio is k0*u²=1/t on the overlap, and remains regular
on the entire original infinity chart, including u=0. -/
theorem infinity_relation : infinityQ R c 0=infinityRatio R c • infinityQ R c 1 := by
  unfold infinityQ infinityRatio
  rw [infinity_coefficients]
  exact weightedSquare_mul _ _ _ _ _ _

variable (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))

theorem global_branch_relation (i : Fin 4) :
    (tensor R c).presheaf.map (homOfLE (show opens R c (some i)≤⊤ from le_top)).op (q R c hN 1)=
      branchRatio R c i •
        (tensor R c).presheaf.map (homOfLE (show opens R c (some i)≤⊤ from le_top)).op (q R c hN 0) := by
  rw [q_restrict,q_restrict]
  exact branch_relation R c i

theorem global_infinity_relation :
    (tensor R c).presheaf.map (homOfLE (show opens R c none≤⊤ from le_top)).op (q R c hN 0)=
      infinityRatio R c •
        (tensor R c).presheaf.map (homOfLE (show opens R c none≤⊤ from le_top)).op (q R c hN 1) := by
  rw [q_restrict,q_restrict]
  exact infinity_relation R c

/-- The actual pair characterizes its finite ratio uniquely in the whole
structure sheaf, rather than only after passing to a fraction field. -/
theorem branch_ratio_unique (i : Fin 4) (a : Γ(scheme R c,opens R c (some i)))
    (h : a • (tensor R c).presheaf.map
      (homOfLE (show opens R c (some i)≤⊤ from le_top)).op (q R c hN 0)=
      (tensor R c).presheaf.map
        (homOfLE (show opens R c (some i)≤⊤ from le_top)).op (q R c hN 1)) :
    a=branchRatio R c i :=
  (IntegralOriginalPairGenerators318.global_branch_generator R c hN i _ le_rfl).1
    (h.trans (global_branch_relation R c hN i))

theorem infinity_ratio_unique (a : Γ(scheme R c,opens R c none))
    (h : a • (tensor R c).presheaf.map
      (homOfLE (show opens R c none≤⊤ from le_top)).op (q R c hN 1)=
      (tensor R c).presheaf.map
        (homOfLE (show opens R c none≤⊤ from le_top)).op (q R c hN 0)) :
    a=infinityRatio R c :=
  (IntegralOriginalPairGenerators318.global_infinity_generator R c hN _ le_rfl).1
    (h.trans (global_infinity_relation R c hN))
end IntegralOriginalSectionRatios318
