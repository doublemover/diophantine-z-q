module
public import IntegralRationalFiveChartGeometry318
public import ContactGlobalBicanonical318
public section
noncomputable section
namespace IntegralOriginalBicanonicalRestrictions318
open AlgebraicGeometry CategoryTheory Opposite
open IntegralRationalFiveChartGeometry318 IntegralRationalGlobalComparison318
open IntrinsicTensorChartSections318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Integer scaling is retained in both actual differential factors' ambient
module; this compares the true section, not only its numerical coefficient. -/
theorem weightedSquare_integer {Y : Scheme} {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (J : ℤ) (a : S) (ω : KaehlerDifferential R S) :
    weightedSquare j p h ((J : S)^2*a) ω = J^2 • weightedSquare j p h a ω := by
  rw [weightedSquare_mul,←Int.cast_smul_eq_zsmul (Γ(Y,j ''ᵁ ⊤))]
  congr 1
  simp only [map_pow,map_intCast,Int.cast_pow]

variable (c : Fin 4 → ℚˣ)
abbrev tensor := ContactGlobalBicanonical318.tensor c
@[expose] def originalQ (n : Fin 2) : Γ(tensor c,⊤) :=
  (VerticalSection318.J^2 : ℤ) •
    (if n=0 then ContactGlobalBicanonical318.q0 c else ContactGlobalBicanonical318.q1 c)

/-- The literal integral branch formula, now viewed in the ORIGINAL model
through the constructed global isomorphism and the same structure map. -/
@[expose] def branchQ (i : Fin 4) (n : Fin 2) :
    Γ(tensor c,branchEmbedding c i ''ᵁ ⊤) :=
  weightedSquare (branchEmbedding c i) (ContactIntrinsicDifferentials318.structureMap c)
    (branch_structure c i) (IntegralGlobalBicanonicalPair318.branchCoefficient ℚ c i n)
    (KaehlerDifferential.D ℚ (IntegralBranchCoordinates318.B ℚ c i)
      (IntegralBranchCoordinates318.sourceCoordinate ℚ c i))

@[expose] def infinityQ (n : Fin 2) : Γ(tensor c,infinityEmbedding c ''ᵁ ⊤) :=
  weightedSquare (infinityEmbedding c) (ContactIntrinsicDifferentials318.structureMap c)
    (infinity_structure c) (IntegralGlobalBicanonicalPair318.infinityCoefficient ℚ c n)
    (KaehlerDifferential.D ℚ (IntegralInfinityChart318.Order ℚ c)
      (IntegralInfinityChart318.coordinate ℚ c))

theorem branch_route (i : Fin 4) :
    Spec.map (IntegralRationalFiniteAtlas318.branchEquiv c i).toRingEquiv.toCommRingCatIso.hom ≫
      branchEmbedding c i = ContactIntrinsicFrames318.branchEmbedding c i := by
  change (branchIso c i).inv ≫
    (IntegralGluedDifferentialFrames318.branchEmbedding ℚ c i ≫ toOriginal c) = _
  rw [branch_toOriginal,Iso.inv_hom_id_assoc]

theorem infinity_route :
    Spec.map (IntegralInfinityOriginalField318.rationalOrderEquiv c).toRingEquiv.toCommRingCatIso.hom ≫
      infinityEmbedding c = InfinityGlobalScheme318.chartEmbedding c := by
  change (infinityIso c).inv ≫ (IntegralGluedModel318.infinityChart ℚ c ≫ toOriginal c) = _
  rw [infinity_toOriginal,Iso.inv_hom_id_assoc]

theorem branchLE (i : Fin 4) : ContactGlobalBicanonical318.opens c (some i) ≤
    branchEmbedding c i ''ᵁ ⊤ := by
  change ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤ ≤ _
  rw [←branch_route]
  exact OpenChartSections318.imageLE _ _

theorem infinityLE : ContactGlobalBicanonical318.opens c none ≤ infinityEmbedding c ''ᵁ ⊤ := by
  change InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤ ≤ _
  rw [←infinity_route]
  exact OpenChartSections318.imageLE _ _

/-- On each entire original finite branch chart, restriction of the actual
integral formula equals restriction of the original global J²-scaled section.
The map transports both the coefficient and universal differential. -/
theorem branch_restriction (i : Fin 4) (n : Fin 2) :
    (tensor c).presheaf.map (homOfLE (branchLE c i)).op (branchQ c i n) =
    (tensor c).presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens c (some i)≤⊤ from le_top)).op
      (originalQ c n) := by
  unfold branchQ
  rw [weightedSquare_restrict_to _ _ _ (IntegralRationalFiniteAtlas318.branchEquiv c i).toAlgHom
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicFrames318.branch_structure c i) (branch_route c i) (branchLE c i)]
  rw [IntegralRationalBranchCoefficients318.scaled_coefficient,
    IntegralRationalBranchCoefficients318.differential,weightedSquare_integer]
  by_cases hn : n=0
  · simp only [hn,ite_true,originalQ,map_zsmul,ContactGlobalBicanonical318.q0_restrict]
    all_goals rfl
  · simp only [hn,ite_false,originalQ,map_zsmul,ContactGlobalBicanonical318.q1_restrict]
    all_goals rfl

/-- The complete original infinity chart receives the same original global
sections, retaining c0^-5, c0^-4 and the exact reciprocal differential. -/
theorem infinity_restriction (n : Fin 2) :
    (tensor c).presheaf.map (homOfLE (infinityLE c)).op (infinityQ c n) =
    (tensor c).presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens c none≤⊤ from le_top)).op
      (originalQ c n) := by
  unfold infinityQ
  rw [weightedSquare_restrict_to _ _ _ (IntegralInfinityOriginalField318.rationalOrderEquiv c).toAlgHom
    (InfinityGlobalScheme318.chartEmbedding c)
    (InfinityStructureSmooth318.chartEmbedding_over_Q c) (infinity_route c) (infinityLE c)]
  rw [IntegralRationalInfinityCoefficients318.scaled_coefficient,
    IntegralRationalInfinityCoefficients318.differential,weightedSquare_integer]
  by_cases hn : n=0
  · simp only [hn,ite_true,originalQ,map_zsmul,ContactGlobalBicanonical318.q0_restrict]
    all_goals rfl
  · simp only [hn,ite_false,originalQ,map_zsmul,ContactGlobalBicanonical318.q1_restrict]
    all_goals rfl
end IntegralOriginalBicanonicalRestrictions318
