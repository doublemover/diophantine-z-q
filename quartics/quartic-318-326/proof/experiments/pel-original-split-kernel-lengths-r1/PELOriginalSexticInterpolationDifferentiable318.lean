module
public import PELOriginalSexticRootInterpolation318
public import DifferentiableFiniteInterpolation318
public section
noncomputable section
namespace PELOriginalSexticInterpolationDifferentiable318
open Set Filter Polynomial QuaternionicRealPeriod318
open scoped Topology
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalOpenPrimitiveSheets318
open PELOriginalLocalizedEvaluationSquare318 PELOriginalPrimitiveLocalReconstruction318
open PELOriginalSexticRootInterpolation318 PELOriginalSexticRatioCover318
open PELOriginalSectionMultiplication318
open AdjoinRootSpecializedPoints318 AdjoinRootSeparablePointCount318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)
variable (hs : Q.Separable)
variable (honto : Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he))

/-- A literal source inverse through EVERY independent root, with complex
differentiability and the SAME original projected base on a genuine
neighborhood. It is produced from full point realization and the original
fixed projection inverse, not from an assumed analytic identification. -/
theorem source_inverse (q : OpenRoots d Q) :
    ∃ z : originalDomain τ hτ j x d,
      originalOpenRootPoint τ hτ j x d Q e he z=q ∧
      ∃ u : ComplexVectors → ComplexVectors,
        u q.val.val.1=z.val ∧ DifferentiableAt ℂ u q.val.val.1 ∧
        ∀ᶠ w in 𝓝 q.val.val.1,
          u w ∈ originalDomain τ hτ j x d ∧ projectedVector τ hτ j x (u w)=w := by
  obtain ⟨z,hz⟩ := honto q
  have hbase : projectedVector τ hτ j x z.val=q.val.val.1 :=
    congrArg (fun r : OpenRoots d Q => r.val.val.1) hz
  obtain ⟨c,hc,hce,hcd⟩ := PELOriginalFixedProjectionInverse318.fixed_projection_chart
    τ hτ j x d Q hs e he z.val z.property.1 z.property.2
  have hcv : c z.val=q.val.val.1 := (hce z.val).trans hbase
  have hinv : c.symm q.val.val.1=z.val := by rw [←hcv,c.left_inv hc]
  have hd : DifferentiableAt ℂ c.symm q.val.val.1 := by
    rw [←hbase]
    exact hcd.differentiableAt (by norm_num)
  have htarget : q.val.val.1 ∈ c.target := hcv ▸ c.map_source hc
  have hdomain : ∀ᶠ w in 𝓝 q.val.val.1,
      c.symm w ∈ originalDomain τ hτ j x d :=
    hd.continuousAt.preimage_mem_nhds
      ((originalDomain_open τ hτ j x d).mem_nhds (hinv.symm ▸ z.property))
  refine ⟨z,hz,c.symm,hinv,hd,?_⟩
  filter_upwards [hdomain,c.open_target.mem_nhds htarget] with w hw hwt
  exact ⟨hw,(hce (c.symm w)).symm.trans (c.right_inv hwt)⟩

/-- Every actual sextic interpolant coefficient is complex differentiable
on the full fixed base open. The finite node list is built from genuine
original source inverses for ALL roots; the values are the original whole
section ratios, never arbitrary holomorphic interpolating data. -/
theorem coefficient_differentiable (hm : Q.Monic) (s : homogeneous τ hτ 6)
    (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0) (n : ℕ) :
    DifferentiableAt ℂ
      (fun w => (interpolant τ hτ j x d Q e he hm s w).coeff n) v := by
  classical
  let V := ComplexPolynomialOpenPoints318.evaluation d v hv
  let I := Roots Q V
  letI : Fintype I := Fintype.ofEquiv ((Q.map V).rootSet ℂ)
    (rootsEquivRootSet Q V hm).symm
  let point (i : I) := LocalizedPrimitiveSelectedPolynomial318.point d Q v hv i
  choose z hz u hu hdu hlocal using fun i : I =>
    source_inverse τ hτ j x d Q e he hs honto (point i)
  let g : I → ComplexVectors → ℂ := fun i w => primitiveValue τ hτ j x d Q e (u i w)
  let a : I → ComplexVectors → ℂ := fun i w => coverRatio τ hτ j s (u i w)
  have hgc (i : I) : g i v=i.val := by
    change primitiveValue τ hτ j x d Q e (u i v)=i.val
    rw [hu i]
    exact congrArg (fun q : OpenRoots d Q => q.val.val.2) (hz i)
  have hgD (i : I) : DifferentiableAt ℂ (g i) v := by
    have hden : algebraEvaluation τ hτ (z i).val j (z i).property.1
        (polynomialMap τ hτ j x d) ≠ 0 := by
      rw [polynomial_evaluation]
      exact (z i).property.2
    have ht : DifferentiableAt ℂ (primitiveValue τ hτ j x d Q e) (z i).val :=
      (PELOriginalLocalizedEvaluationRegularity318.contDiffAt_evaluate τ hτ j
        (polynomialMap τ hτ j x d) (e (AdjoinRoot.root Q)) (z i).val
        (z i).property.1 hden).differentiableAt (by norm_num)
    have ht' : DifferentiableAt ℂ (primitiveValue τ hτ j x d Q e) (u i v) := (hu i).symm ▸ ht
    exact ht'.comp v (hdu i)
  have haD (i : I) : DifferentiableAt ℂ (a i) v := by
    have ht : DifferentiableAt ℂ (coverRatio τ hτ j s) (z i).val :=
      (PELOriginalPowerSectionLift318.entire τ hτ 6
        (PELOriginalWholeHZeroDimension318.asSection τ hτ 6 s) (z i).val).div
        ((holomorphic τ hτ 3 j (z i).val).pow 2) (pow_ne_zero 2 (z i).property.1)
    have ht' : DifferentiableAt ℂ (coverRatio τ hτ j s) (u i v) := (hu i).symm ▸ ht
    exact ht'.comp v (hdu i)
  have hdistinct : ∀ᶠ w in 𝓝 v, Function.Injective (fun i => g i w) := by
    have hh : ∀ᶠ w in 𝓝 v, ∀ i j : I, i ≠ j → g i w ≠ g j w := by
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro k
      by_cases hik : i=k
      · exact Filter.Eventually.of_forall (fun _ h => (h hik).elim)
      · have hc : g i v-g k v ≠ 0 := by
          rw [hgc,hgc]
          exact sub_ne_zero.mpr (fun h => hik (Subtype.ext h))
        filter_upwards [((hgD i).continuousAt.sub (hgD k).continuousAt).eventually_ne hc] with w hw _
        exact sub_ne_zero.mp hw
    filter_upwards [hh] with w hw i k hik
    by_contra hne
    exact hw i k hne hik
  have hdomains : ∀ᶠ w in 𝓝 v, ∀ i : I,
      u i w ∈ originalDomain τ hτ j x d ∧ projectedVector τ hτ j x (u i w)=w :=
    Filter.eventually_all.mpr hlocal
  have hD : ∀ᶠ w in 𝓝 v, MvPolynomial.eval w d ≠ 0 :=
    (((AnalyticOnNhd.eval_mvPolynomial d) v (mem_univ v)).continuousAt).eventually_ne hv
  have hcard : (Finset.univ : Finset I).card=Q.natDegree := by
    change Fintype.card I=Q.natDegree
    rw [Fintype.card_congr (rootsEquivRootSet Q V hm),
      Polynomial.card_rootSet_eq_natDegree hs.map (IsAlgClosed.splits _)]
    exact hm.natDegree_map V
  have hinterp := DifferentiableFiniteInterpolation318.coefficient Finset.univ g a v
    (fun i _ => hgD i) (fun i _ => haD i)
    (fun i _ k _ hik => Subtype.ext (by simpa only [hgc] using hik)) n
  apply hinterp.congr_of_eventuallyEq
  filter_upwards [hdomains,hdistinct,hD] with w hw hi hwd
  have hroot (i : I) : LocalizedPrimitiveRootChart318.equation d Q (w,g i w)=0 := by
    have hr := original_root τ hτ j x d Q e he (u i w) (hw i).1.1 (hw i).1.2
    simpa only [(hw i).2,g] using hr
  have hvalue (i : I) : rootValue τ hτ j x d Q e he s
      ⟨⟨(w,g i w),hroot i⟩,hwd⟩=a i w := by
    let zz : originalDomain τ hτ j x d := ⟨u i w,(hw i).1⟩
    have heq : originalOpenRootPoint τ hτ j x d Q e he zz=
        (⟨⟨(w,g i w),hroot i⟩,hwd⟩ : OpenRoots d Q) := by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (hw i).2 rfl
    rw [←heq,rootValue_original]
    rfl
  exact congrArg (fun P : Polynomial ℂ => P.coeff n)
    (LocalizedRootInterpolation318.enumeration_eq d Q hm hs (rootValue τ hτ j x d Q e he s)
      w hwd Finset.univ (fun i => g i w) (fun i => a i w) hcard hi.injOn
      (fun i _ => hroot i) (fun i _ => hvalue i))
end PELOriginalSexticInterpolationDifferentiable318
