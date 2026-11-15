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

/-- Conditional coefficient transport before specializing concrete chart carriers. -/
theorem weightedSquare_ite {Y : Scheme} {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (P : Prop) [Decidable P] (a b : S) (ω : KaehlerDifferential R S) :
    weightedSquare j p h (if P then a else b) ω =
      if P then weightedSquare j p h a ω else weightedSquare j p h b ω := by
  split <;> rfl

/-- Abstract route transport handles the proof-dependent open-image instance
before specializing the original complete chart. -/
theorem imageLE_of_route {X Y Z : Scheme} (k : Z ⟶ X) (j : X ⟶ Y)
    [IsOpenImmersion k] [IsOpenImmersion j] (jT : Z ⟶ Y) [IsOpenImmersion jT]
    (route : k ≫ j=jT) : jT ''ᵁ ⊤ ≤ j ''ᵁ ⊤ := by
  subst jT
  exact OpenChartSections318.imageLE k j

/-- Pin the actual algebra-equivalence map while carriers are abstract. -/
theorem spec_algEquiv_open {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom)) := by
  change IsOpenImmersion (Spec.map e.toRingEquiv.toCommRingCatIso.hom)
  infer_instance

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
  exact imageLE_of_route _ _ _ (branch_route c i)

theorem infinityLE : ContactGlobalBicanonical318.opens c none ≤ infinityEmbedding c ''ᵁ ⊤ := by
  change InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤ ≤ _
  exact imageLE_of_route _ _ _ (infinity_route c)

/-- On each entire original finite branch chart, restriction of the actual
integral formula equals restriction of the original global J²-scaled section.
The map transports both the coefficient and universal differential. -/
theorem branch_restriction (i : Fin 4) (n : Fin 2) :
    (tensor c).presheaf.map (homOfLE (branchLE c i)).op (branchQ c i n) =
    (tensor c).presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens c (some i)≤⊤ from le_top)).op
      (originalQ c n) := by
  letI := spec_algEquiv_open (IntegralRationalFiniteAtlas318.branchEquiv c i)
  have transport :
      (tensor c).presheaf.map (homOfLE (branchLE c i)).op (branchQ c i n) =
        weightedSquare (ContactIntrinsicFrames318.branchEmbedding c i)
          (ContactIntrinsicDifferentials318.structureMap c)
          (ContactIntrinsicFrames318.branch_structure c i)
          ((IntegralRationalFiniteAtlas318.branchEquiv c i).toAlgHom
            (IntegralGlobalBicanonicalPair318.branchCoefficient ℚ c i n))
          (AlgHomDifferential318.map (IntegralRationalFiniteAtlas318.branchEquiv c i).toAlgHom
            (KaehlerDifferential.D ℚ (IntegralBranchCoordinates318.B ℚ c i)
              (IntegralBranchCoordinates318.sourceCoordinate ℚ c i))) :=
    weightedSquare_restrict_to
      (R := ℚ) (S := IntegralBranchCoordinates318.B ℚ c i)
      (T := ContactIntrinsicFrames318.BranchRing c i)
      (branchEmbedding c i) (ContactIntrinsicDifferentials318.structureMap c)
      (branch_structure c i) (IntegralRationalFiniteAtlas318.branchEquiv c i).toAlgHom
      (ContactIntrinsicFrames318.branchEmbedding c i)
      (ContactIntrinsicFrames318.branch_structure c i) (branch_route c i) (branchLE c i)
      (IntegralGlobalBicanonicalPair318.branchCoefficient ℚ c i n)
      (KaehlerDifferential.D ℚ (IntegralBranchCoordinates318.B ℚ c i)
        (IntegralBranchCoordinates318.sourceCoordinate ℚ c i))
  -- Compose already typed equalities; rewriting the specialized section
  -- goal exposes semireducible open/tensor carriers at implicit transparency.
  have values := congrArg₂
    (fun (a : ContactIntrinsicFrames318.BranchRing c i) (ω : KaehlerDifferential ℚ (ContactIntrinsicFrames318.BranchRing c i)) =>
      weightedSquare (R := ℚ) (S := ContactIntrinsicFrames318.BranchRing c i)
        (ContactIntrinsicFrames318.branchEmbedding c i) (ContactIntrinsicDifferentials318.structureMap c)
        (ContactIntrinsicFrames318.branch_structure c i) a ω)
    (IntegralRationalBranchCoefficients318.scaled_coefficient c i n)
    (IntegralRationalBranchCoefficients318.differential c i)
  have scaled := weightedSquare_integer (R := ℚ) (S := ContactIntrinsicFrames318.BranchRing c i)
    (ContactIntrinsicFrames318.branchEmbedding c i) (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i) VerticalSection318.J
    (if n=0 then ContactBicanonicalCoefficients318.branchQ0 c i else ContactBicanonicalCoefficients318.branchQ1 c i)
    (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i) (ContactFrameNormalization318.sourceCoordinate c i))
  have localValue := weightedSquare_ite (R := ℚ) (S := ContactIntrinsicFrames318.BranchRing c i)
    (ContactIntrinsicFrames318.branchEmbedding c i) (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i) (n=0)
    (ContactBicanonicalCoefficients318.branchQ0 c i) (ContactBicanonicalCoefficients318.branchQ1 c i)
    (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i) (ContactFrameNormalization318.sourceCoordinate c i))
  have scaledLocal := congrArg (fun x : Γ(tensor c,ContactGlobalBicanonical318.opens c (some i)) =>
    (VerticalSection318.J^2 : ℤ) • x) localValue
  have originalRestriction :
      (tensor c).presheaf.map
        (homOfLE (show ContactGlobalBicanonical318.opens c (some i)≤⊤ from le_top)).op
        (originalQ c n) =
      (VerticalSection318.J^2 : ℤ) •
        (if n=0 then ContactGlobalBicanonical318.localQ0 c (some i)
          else ContactGlobalBicanonical318.localQ1 c (some i)) := by
    by_cases hn : n=0
    · simp only [originalQ,hn,ite_true,map_zsmul,ContactGlobalBicanonical318.q0_restrict]
    · simp only [originalQ,hn,ite_false,map_zsmul,ContactGlobalBicanonical318.q1_restrict]
  exact transport.trans (values.trans (scaled.trans (scaledLocal.trans originalRestriction.symm)))

/-- The complete original infinity chart receives the same original global
sections, retaining c0^-5, c0^-4 and the exact reciprocal differential. -/
theorem infinity_restriction (n : Fin 2) :
    (tensor c).presheaf.map (homOfLE (infinityLE c)).op (infinityQ c n) =
    (tensor c).presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens c none≤⊤ from le_top)).op
      (originalQ c n) := by
  letI := spec_algEquiv_open (IntegralInfinityOriginalField318.rationalOrderEquiv c)
  have transport :
      (tensor c).presheaf.map (homOfLE (infinityLE c)).op (infinityQ c n) =
        weightedSquare (InfinityGlobalScheme318.chartEmbedding c)
          (ContactIntrinsicDifferentials318.structureMap c)
          (InfinityStructureSmooth318.chartEmbedding_over_Q c)
          ((IntegralInfinityOriginalField318.rationalOrderEquiv c).toAlgHom
            (IntegralGlobalBicanonicalPair318.infinityCoefficient ℚ c n))
          (AlgHomDifferential318.map (IntegralInfinityOriginalField318.rationalOrderEquiv c).toAlgHom
            (KaehlerDifferential.D ℚ (IntegralInfinityChart318.Order ℚ c)
              (IntegralInfinityChart318.coordinate ℚ c))) :=
    weightedSquare_restrict_to
      (R := ℚ) (S := IntegralInfinityChart318.Order ℚ c)
      (T := InfinityGlobalChart318.InfinityOrder c)
      (infinityEmbedding c) (ContactIntrinsicDifferentials318.structureMap c)
      (infinity_structure c) (IntegralInfinityOriginalField318.rationalOrderEquiv c).toAlgHom
      (InfinityGlobalScheme318.chartEmbedding c)
      (InfinityStructureSmooth318.chartEmbedding_over_Q c) (infinity_route c) (infinityLE c)
      (IntegralGlobalBicanonicalPair318.infinityCoefficient ℚ c n)
      (KaehlerDifferential.D ℚ (IntegralInfinityChart318.Order ℚ c)
        (IntegralInfinityChart318.coordinate ℚ c))
  -- Compose already typed equalities; rewriting the specialized section
  -- goal exposes semireducible open/tensor carriers at implicit transparency.
  have values := congrArg₂
    (fun (a : InfinityGlobalChart318.InfinityOrder c) (ω : KaehlerDifferential ℚ (InfinityGlobalChart318.InfinityOrder c)) =>
      weightedSquare (R := ℚ) (S := InfinityGlobalChart318.InfinityOrder c)
        (InfinityGlobalScheme318.chartEmbedding c) (ContactIntrinsicDifferentials318.structureMap c)
        (InfinityStructureSmooth318.chartEmbedding_over_Q c) a ω)
    (IntegralRationalInfinityCoefficients318.scaled_coefficient c n)
    (IntegralRationalInfinityCoefficients318.differential c)
  have scaled := weightedSquare_integer (R := ℚ) (S := InfinityGlobalChart318.InfinityOrder c)
    (InfinityGlobalScheme318.chartEmbedding c) (ContactIntrinsicDifferentials318.structureMap c)
    (InfinityStructureSmooth318.chartEmbedding_over_Q c) VerticalSection318.J
    (if n=0 then ContactBicanonicalCoefficients318.infinityQ0 c else ContactBicanonicalCoefficients318.infinityQ1 c)
    (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c) (ContactFrameNormalization318.infinityCoordinate c))
  have localValue := weightedSquare_ite (R := ℚ) (S := InfinityGlobalChart318.InfinityOrder c)
    (InfinityGlobalScheme318.chartEmbedding c) (ContactIntrinsicDifferentials318.structureMap c)
    (InfinityStructureSmooth318.chartEmbedding_over_Q c) (n=0)
    (ContactBicanonicalCoefficients318.infinityQ0 c) (ContactBicanonicalCoefficients318.infinityQ1 c)
    (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c) (ContactFrameNormalization318.infinityCoordinate c))
  have scaledLocal := congrArg (fun x : Γ(tensor c,ContactGlobalBicanonical318.opens c none) =>
    (VerticalSection318.J^2 : ℤ) • x) localValue
  have originalRestriction :
      (tensor c).presheaf.map
        (homOfLE (show ContactGlobalBicanonical318.opens c none≤⊤ from le_top)).op
        (originalQ c n) =
      (VerticalSection318.J^2 : ℤ) •
        (if n=0 then ContactGlobalBicanonical318.localQ0 c none
          else ContactGlobalBicanonical318.localQ1 c none) := by
    by_cases hn : n=0
    · simp only [originalQ,hn,ite_true,map_zsmul,ContactGlobalBicanonical318.q0_restrict]
    · simp only [originalQ,hn,ite_false,map_zsmul,ContactGlobalBicanonical318.q1_restrict]
  exact transport.trans (values.trans (scaled.trans (scaledLocal.trans originalRestriction.symm)))
end IntegralOriginalBicanonicalRestrictions318
