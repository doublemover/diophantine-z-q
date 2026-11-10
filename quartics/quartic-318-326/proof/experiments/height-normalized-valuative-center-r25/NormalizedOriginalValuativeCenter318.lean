module
public import NormalizedValuativeChartStructure318
public section
noncomputable section
namespace NormalizedOriginalValuativeCenter318
open Polynomial CategoryTheory AlgebraicGeometry NormalizedWholeOverlap318 NormalizedWholeGluing318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- One common local square normalization of the ORIGINAL four twists gives
an actual section of the whole proper V-model whose generic point is the
specified entire signed root map. The finite/nonintegral-coordinate cases
use the same coefficients and multiplier choices. No good-prime exclusion,
unit-twist premise, regularity, or abstract valuative extension is assumed. -/
theorem exists_center (pi : V) (hp : Irreducible pi) (c : Fin 4 → Kˣ)
    (a : Fin 4 → V) (t : K) (y : Fin 4 → K)
    (hy : ∀ i,(y i)^2=(c i:K)*(t-algebraMap V K (a i))) :
    ∃ (u : Fin 4 → Vˣ) (e : Fin 4 → Fin 2) (s : Fin 4 → K)
      (hs : ∀ i,s i≠0)
      (hc : ∀ i,(c i:K)=algebraMap V K ((u i:V)*pi^(e i:ℕ))*(s i)^2)
      (g : Spec (CommRingCat.of V) ⟶
        scheme V (fun i => (u i:V)*pi^(e i:ℕ)) a),
      g ≫ NormalizedWholeProjection318.structureMap V
        (fun i => (u i:V)*pi^(e i:ℕ)) a=𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g=
        NormalizedGenericPointExtension318.point V K
          (fun i => (u i:V)*pi^(e i:ℕ)) a t (fun i => y i/s i)
          (fun i => DVRNormalizedContactPoint318.root_relation _ _ _ _ _ _ (hs i) (hc i) (hy i)) := by
  obtain ⟨u,e,s,hs,hc,hcharts⟩ := DVRNormalizedAllPlaceCharts318.chart_center V K pi hp c a t y hy
  refine ⟨u,e,s,hs,hc,?_⟩
  let d : Fin 4 → V := fun i => (u i:V)*pi^(e i:ℕ)
  have hz (i : Fin 4) : (y i/s i)^2=algebraMap V K (d i)*(t-algebraMap V K (a i)) :=
    DVRNormalizedContactPoint318.root_relation _ _ _ _ _ _ (hs i) (hc i) (hy i)
  rcases hcharts with ⟨T,f,hT,hf,hr⟩ | ⟨w,f,ht,hw,hwn,hf,hr⟩
  · refine ⟨Spec.map (CommRingCat.ofHom f) ≫ finiteChart V d a,
      NormalizedValuativeChartStructure318.finite_section V d a T f hf,?_⟩
    apply NormalizedGenericPointExtension318.finite_extension V K d a t (fun i => y i/s i) hz T hT f hf
    intro i
    apply (eq_div_iff (hs i)).2
    simpa only [mul_comm] using hr i
  · refine ⟨Spec.map (CommRingCat.ofHom f) ≫ infinityChart V d a,
      NormalizedValuativeChartStructure318.infinity_section V d a w f hf,?_⟩
    apply NormalizedGenericPointExtension318.infinity_extension V K d a t (fun i => y i/s i) hz ht w hw f hf
    intro i
    apply (eq_div_iff ht).2
    apply (eq_div_iff (hs i)).2
    calc
      _ = s i*t*algebraMap V K (f (FourRootOrderSigns318.generator
          (DVRNormalizedInfinityOrder318.coefficient V d a) i)) := by ring
      _ = y i := hr i
end NormalizedOriginalValuativeCenter318
