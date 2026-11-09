module
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Algebra.Group.Subgroup
public section
noncomputable section

/-! A genuine finite-product Kronecker criterion. The proof compares normalized
Haar integration on the actual closed cyclic subgroup with integration on the
whole torus. Equality on characters extends by uniform Fourier density. A
continuous distance function then rules out a proper closed subgroup. -/
namespace TorusCharacterDensity318
open Set MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped BigOperators
set_option maxHeartbeats 2000000

section Haar
variable (X : Type*) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

@[expose] def probabilityHaar : Measure X := Measure.addHaarMeasure (⊤ : PositiveCompacts X)

instance probabilityHaar_probability : IsProbabilityMeasure (probabilityHaar X) := by
  constructor
  simpa [probabilityHaar] using
    (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts X)))

instance probabilityHaar_invariant : Measure.IsAddLeftInvariant (probabilityHaar X) := by
  unfold probabilityHaar
  infer_instance

instance probabilityHaar_positive : IsOpenPosMeasure (probabilityHaar X) := by
  unfold probabilityHaar
  infer_instance
end Haar

section Average
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y]
  (μ : Measure X) [IsProbabilityMeasure μ] (c : C(X,Y))

private lemma continuous_integrable (f : C(Y,ℂ)) : Integrable (fun x => f (c x)) μ :=
  (f.continuous.comp c.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Integration after a fixed continuous map, with norm at most one. -/
@[expose] def average : C(Y,ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f (c x) ∂μ
      map_add' := fun f g => integral_add (continuous_integrable μ c f) (continuous_integrable μ c g)
      map_smul' := fun z f => integral_smul z (fun x => f (c x)) }
    1 (by
      intro f
      simpa using (norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm (c x))))

lemma average_apply (f : C(Y,ℂ)) : average μ c f=∫ x, f (c x) ∂μ := rfl
end Average

variable {d : Type*} [Fintype d]

lemma character_add (n : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier n (x+y)=UnitAddTorus.mFourier n x*UnitAddTorus.mFourier n y := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,
    zsmul_add,AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]

private lemma character_integral_zero
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (c : X →+ UnitAddTorus d) (n : d → ℤ) (a : X)
    (ha : UnitAddTorus.mFourier n (c a)≠1) :
    (∫ x, UnitAddTorus.mFourier n (c x) ∂probabilityHaar X)=0 := by
  have he := integral_add_left_eq_self (μ := probabilityHaar X)
    (fun x => UnitAddTorus.mFourier n (c x)) a
  simp_rw [map_add,character_add] at he
  rw [integral_const_mul] at he
  have hz : (UnitAddTorus.mFourier n (c a)-1)*
      (∫ x, UnitAddTorus.mFourier n (c x) ∂probabilityHaar X)=0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

/-- No nontrivial integer character annihilates the generator: this is the
precise hypothesis needed for full-product density, rather than merely
infinite order or independence in an unspecified compact group. -/
theorem denseRange_zsmul (a : UnitAddTorus d)
    (ha : ∀ n : d → ℤ, n≠0 → UnitAddTorus.mFourier n a≠1) :
    DenseRange (fun k : ℤ => k • a) := by
  classical
  let H : AddSubgroup (UnitAddTorus d) := (AddSubgroup.zmultiples a).topologicalClosure
  have hH : IsClosed (H : Set (UnitAddTorus d)) := AddSubgroup.isClosed_topologicalClosure _
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let ah : H := ⟨a,AddSubgroup.le_topologicalClosure _ (AddSubgroup.mem_zmultiples a)⟩
  let inclusion : C(H,UnitAddTorus d) := ⟨Subtype.val,continuous_subtype_val⟩
  let A := average (probabilityHaar H) inclusion
  let B := average (probabilityHaar (UnitAddTorus d)) (ContinuousMap.id _)
  have hchar : ∀ n : d → ℤ, A (UnitAddTorus.mFourier n)=B (UnitAddTorus.mFourier n) := by
    intro n
    by_cases hn : n=0
    · subst n
      simp [A,B,average_apply,UnitAddTorus.mFourier_zero]
    · change (∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂probabilityHaar H)=
        ∫ x, UnitAddTorus.mFourier n x ∂probabilityHaar (UnitAddTorus d)
      rw [character_integral_zero H.subtype n ah (ha n hn),
        character_integral_zero (AddMonoidHom.id (UnitAddTorus d)) n a (ha n hn)]
  have hspan : (Submodule.span ℂ (range (UnitAddTorus.mFourier (d := d))) :
      Set C(UnitAddTorus d,ℂ)) ⊆ {f | A f=B f} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨n,rfl⟩ := hx; exact hchar n
    | zero => simp
    | add x y hx hy hxy hyy => simpa only [map_add,hxy,hyy]
    | smul z x hx he => simpa only [map_smul,he]
  have hclosure := closure_minimal hspan (isClosed_eq A.continuous B.continuous)
  have htop : closure ((Submodule.span ℂ (range (UnitAddTorus.mFourier (d := d))) :
      Submodule ℂ C(UnitAddTorus d,ℂ)) : Set C(UnitAddTorus d,ℂ))=univ := by
    exact congrArg (fun S : Submodule ℂ C(UnitAddTorus d,ℂ) => (S : Set C(UnitAddTorus d,ℂ)))
      UnitAddTorus.span_mFourier_closure_eq_top
  have hall : ∀ f, A f=B f := by
    intro f
    exact hclosure (htop.symm ▸ mem_univ f)
  let f : C(UnitAddTorus d,ℂ) :=
    ⟨fun x => (Metric.infDist x (H : Set (UnitAddTorus d)) : ℂ),
      Complex.continuous_ofReal.comp (Metric.continuous_infDist_pt _)⟩
  have hAzero : A f=0 := by
    change (∫ x : H, (Metric.infDist (x : UnitAddTorus d) (H : Set (UnitAddTorus d)) : ℂ)
      ∂probabilityHaar H)=0
    calc
      _ = ∫ _x : H, (0 : ℂ) ∂probabilityHaar H := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by rw [Metric.infDist_zero_of_mem x.property]; rfl
      _ = 0 := integral_zero _ _
  have hreal : (∫ x, Metric.infDist x (H : Set (UnitAddTorus d))
      ∂probabilityHaar (UnitAddTorus d))=0 := by
    have he := (hall f).symm.trans hAzero
    change (∫ x, (Metric.infDist x (H : Set (UnitAddTorus d)) : ℂ)
      ∂probabilityHaar (UnitAddTorus d))=0 at he
    rw [integral_complex_ofReal] at he
    exact Complex.ofReal_injective he
  have hfi : Integrable (fun x => Metric.infDist x (H : Set (UnitAddTorus d)))
      (probabilityHaar (UnitAddTorus d)) :=
    (Metric.continuous_infDist_pt _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => Metric.infDist_nonneg) hfi).mp hreal
  have hevery : (fun x => Metric.infDist x (H : Set (UnitAddTorus d)))=fun _ => 0 :=
    MeasureTheory.Measure.eq_of_ae_eq hae (Metric.continuous_infDist_pt _) continuous_const
  have heq : (H : Set (UnitAddTorus d))=univ := by
    apply eq_univ_of_forall
    intro x
    exact (hH.mem_iff_infDist_zero ⟨0,H.zero_mem⟩).mpr (congrFun hevery x)
  change Dense (range (fun k : ℤ => k • a))
  apply dense_iff_closure_eq.mpr
  exact heq

end TorusCharacterDensity318
