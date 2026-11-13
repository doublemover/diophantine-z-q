module
public import FourRootGluedScheme318
public import FourRootInfinitySmooth318
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.Sets.OpenCover
public section
noncomputable section
namespace FourRootWholeSchemeGeometry318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open FourRootGluedScheme318 FourRootCoordinateOverlap318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)

@[expose] def twoChartCover:(scheme b).OpenCover where
  I₀:=Bool
  X k:=if k then finiteScheme b else infinityScheme b
  f k:=by cases k;exact infinityChart b;exact finiteChart b
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      rcases charts_cover b p with ⟨q,hq⟩|⟨q,hq⟩
      · exact ⟨true,q,hq⟩
      · exact ⟨false,q,hq⟩
    · intro k;cases k <;> infer_instance

lemma chart_intersection:
    ((finiteChart b).opensRange⊓(infinityChart b).opensRange:(scheme b).Opens)≠⊥:=by
  letI:IsDomain (InfinityOverlap b):=FourRootInfinityDomain318.infinity_overlap_domain b hb
  obtain ⟨p⟩:Nonempty (overlapScheme b):=inferInstance
  intro h
  have hp:finiteChart b (intoFinite b p)∈
      ((finiteChart b).opensRange⊓(infinityChart b).opensRange):=by
    refine ⟨⟨_,rfl⟩,⟨intoInfinity b p,?_⟩⟩
    change (intoInfinity b≫infinityChart b) p=(intoFinite b≫finiteChart b) p
    rw [chart_overlap]
  rw [h] at hp
  exact hp

/-- Irreducibility belongs to the WHOLE glued Scheme. The two genuine
integral affine charts have a nonempty actual localization intersection. -/
theorem irreducible:IrreducibleSpace (scheme b):=by
  letI:IsDomain (Affine b):=FourRootActualGenericField318.affine_domain b hb
  letI:IsDomain (Infinity b):=FourRootInfinityDomain318.infinity_domain b hb
  let U:Bool→(scheme b).Opens:=fun k=>
    if k then (finiteChart b).opensRange else (infinityChart b).opensRange
  have hi:∀k:Bool,IsPreirreducible (U k:Set (scheme b)):=by
    intro k
    cases k
    · simpa [U,Set.image_univ] using
        (PreirreducibleSpace.isPreirreducible_univ (X:=infinityScheme b)).image
          (infinityChart b) (infinityChart b).continuous.continuousOn
    · simpa [U,Set.image_univ] using
        (PreirreducibleSpace.isPreirreducible_univ (X:=finiteScheme b)).image
          (finiteChart b) (finiteChart b).continuous.continuousOn
  have hn:Pairwise (fun i j=>¬Disjoint (U i) (U j)):=by
    intro i j hij
    cases i <;> cases j <;> simp only [ne_eq,not_true_eq_false] at hij
    · simpa [U,disjoint_iff,inf_comm] using chart_intersection b hb
    · simpa [U,disjoint_iff] using chart_intersection b hb
  have hu:(Set.univ:Set (scheme b))⊆⋃k:Bool,(U k:Set (scheme b)):=by
    intro p _
    rcases charts_cover b p with ⟨q,hq⟩|⟨q,hq⟩
    · exact mem_iUnion.mpr ⟨true,q,hq⟩
    · exact mem_iUnion.mpr ⟨false,q,hq⟩
  rw [irreducibleSpace_def]
  exact ⟨⟨finiteChart b (Classical.choice inferInstance),mem_univ _⟩,
    IsPreirreducible.of_subset_iUnion hn hi isOpen_univ hu⟩

theorem reduced:IsReduced (scheme b):=by
  letI:IsDomain (Affine b):=FourRootActualGenericField318.affine_domain b hb
  letI:IsDomain (Infinity b):=FourRootInfinityDomain318.infinity_domain b hb
  haveI:∀k,IsReduced ((twoChartCover b).X k):=by
    intro k
    cases k <;> change IsReduced (Spec (CommRingCat.of _)) <;> infer_instance
  exact IsReduced.of_openCover _ (twoChartCover b)
theorem integral:IsIntegral (scheme b):=by
  letI:=irreducible b hb
  letI:=reduced b hb
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Smoothness descends from the WHOLE actual finite and infinity
quotients, including every branch and all eight infinity points. -/
theorem smooth:Smooth (structureMap b):=by
  have hf:Smooth (finiteBase b):=(HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (FourRootAffineSmooth318.smooth b hb))
  have hi:Smooth (infinityBase b):=(HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (FourRootInfinitySmooth318.smooth b hb))
  apply IsZariskiLocalAtSource.of_openCover (twoChartCover b)
  intro k
  cases k
  · change Smooth (infinityChart b≫structureMap b)
    rw [infinity_structure]
    exact hi
  · change Smooth (finiteChart b≫structureMap b)
    rw [finite_structure]
    exact hf

/-- Normality of a chart is transported to the actual section ring and
then its genuine stalk localization, not to an auxiliary abstract ring. -/
lemma normal_stalk_of_chart {Y:Scheme} (R:Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (j:Spec (CommRingCat.of R)⟶Y) [IsOpenImmersion j]
    (p:Spec (CommRingCat.of R)):
    IsIntegrallyClosed (Y.presheaf.stalk (j p)):=by
  let U:Y.affineOpens:=⟨j.opensRange,isAffineOpen_opensRange j⟩
  let e:R≃+*Γ(Y,U):=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).symm≪≫IsOpenImmersion.ΓIsoTop j).commRingCatIsoToRingEquiv
  letI:IsDomain Γ(Y,U):=Function.Injective.isDomain e.symm e.symm.injective
  letI:IsIntegrallyClosed Γ(Y,U):=IsIntegrallyClosed.of_equiv e
  let x:U:=⟨j p,⟨p,rfl⟩⟩
  letI:=Y.presheaf.algebra_section_stalk x
  letI:=U.2.isLocalization_stalk x
  exact isIntegrallyClosed_of_isLocalization _ (U.2.primeIdealOf x).asIdeal.primeCompl
    (U.2.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors

theorem normal_stalk (p:scheme b):IsIntegrallyClosed ((scheme b).presheaf.stalk p):=by
  letI:IsDomain (Affine b):=FourRootActualGenericField318.affine_domain b hb
  letI:IsDomain (Infinity b):=FourRootInfinityDomain318.infinity_domain b hb
  letI:IsIntegrallyClosed (Affine b):=FourRootAffineSmooth318.integrallyClosed b hb
  letI:IsIntegrallyClosed (Infinity b):=FourRootInfinitySmooth318.integrallyClosed b hb
  rcases charts_cover b p with ⟨q,rfl⟩|⟨q,rfl⟩
  · exact normal_stalk_of_chart (Affine b) (finiteChart b) q
  · exact normal_stalk_of_chart (Infinity b) (infinityChart b) q

/-- Every input is constructed from distinct branch values; no normal,
smooth or irreducible-source hypothesis is supplied. -/
theorem whole_geometry:IsIntegral (scheme b) ∧ Smooth (structureMap b) ∧
    ∀p:scheme b,IsIntegrallyClosed ((scheme b).presheaf.stalk p):=
  ⟨integral b hb,smooth b hb,normal_stalk b hb⟩
end FourRootWholeSchemeGeometry318
