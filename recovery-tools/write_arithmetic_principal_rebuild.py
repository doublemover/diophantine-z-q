from pathlib import Path
import shutil
root=Path(__file__).resolve().parents[1]; b=root/'quartics/quartic-318-326/proof/experiments';old=b/'forward-actual-two-descent-original-support-rebuild-r1';p=b/'forward-actual-two-descent-original-principal-certificate-rebuild-r1'
if not p.exists():shutil.copytree(old,p)
shutil.copy2(b/'height-original-all-place-metric-r1/ActualDvrMeromorphicOrder318.lean',p/'ActualDvrMeromorphicOrder318.lean')
sources={
'ActualTwoDescentOriginalInfinityStalkPoleRebuild318':'''module
public import ActualTwoDescentOriginalAllPointRootSupportRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityStalkPoleRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityNativeFractionFunctions318
variable {K : Type*} [Field K] [CharZero K]

/-- The SAME original generic function, original infinity stalk and actual
local units. This is not an arbitrary field identification. -/
theorem factor (n a : K) :
    ∃ e d : (InfinityStalk n)ˣ,
      infinityV n=(e : InfinityStalk n)*infinityU n^3 ∧
      ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a *
        (algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (infinityU n))^2 =
        algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (d : InfinityStalk n) /
          algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (e : InfinityStalk n) := by
  obtain ⟨e,d,he,hd,hv,hr,hunit⟩ :=
    ActualTwoDescentOriginalInfinityNamedPoleRebuild318.normalization n a
  refine ⟨Units.map (infinityEquiv n).symm.toMonoidHom e,
    Units.map (infinityEquiv n).symm.toMonoidHom d, ?_, ?_⟩
  · simpa only [infinityV,infinityU,map_mul,map_pow,Units.coe_map] using
      congrArg (infinityEquiv n).symm he
  · apply (ActualTwoDescentOriginalInfinityLocalFieldRebuild318.comparison n).injective
    simpa only [map_mul,map_pow,map_div₀,
      ActualTwoDescentOriginalInfinityLocalFieldRebuild318.on_stalk,
      infinityU,Units.coe_map,RingEquiv.apply_symm_apply] using hr

theorem fraction (n a : K) :
    ∃ e d : (InfinityStalk n)ˣ,
      ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a =
        (algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (d : InfinityStalk n) /
          algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (e : InfinityStalk n)) /
        (algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (infinityU n))^2 := by
  obtain ⟨e,d,he,hd⟩ := factor n a
  have hu : algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (infinityU n) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (ActualTwoDescentOriginalStalkFactorsRebuild318.infinity_uniformizer n).ne_zero
  exact ⟨e,d,(eq_div_iff (pow_ne_zero 2 hu)).mpr hd⟩
end ActualTwoDescentOriginalInfinityStalkPoleRebuild318
''',
'ActualTwoDescentOriginalRootMeromorphicOrderRebuild318':'''module
public import ActualTwoDescentOriginalInfinityStalkPoleRebuild318
public import ActualDvrMeromorphicOrder318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootMeromorphicOrderRebuild318
open AlgebraicGeometry IsDiscreteValuationRing
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Native normalized valuation on the actual original generic field,
not a separately selected rational-function field. -/
def value (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    AddValuation (originalCubicScheme n).functionField (WithTop ℤ) :=
  ActualDvrMeromorphicOrder318.value (RootStalk n i) (originalCubicScheme n).functionField

theorem named_root (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    value n i (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
      (ActualTwoDescentOriginalRootIdeals318.root n i)) = (2 : WithTop ℤ) := by
  rw [←ActualTwoDescentOriginalRootGenericSquareRebuild318.root_square]
  change ActualDvrMeromorphicOrder318.value (RootStalk n i) _ _ = _
  rw [ActualDvrMeromorphicOrder318.value_integral _ _ _
    (ActualTwoDescentOriginalRootGenericSquareRebuild318.root_nonzero_in_stalk n i),
    ActualTwoDescentOriginalStalkOrdersRebuild318.root_f_order]
  norm_num

theorem integral_order (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    ActualDvrMeromorphicOrder318.order (RootStalk n i) (originalCubicScheme n).functionField
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i)) = 2 :=
  ActualDvrMeromorphicOrder318.order_eq _ _ _ 2 (named_root n i)
end ActualTwoDescentOriginalRootMeromorphicOrderRebuild318
''',
'ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318':'''module
public import ActualTwoDescentOriginalRootMeromorphicOrderRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

def value (n : K) : AddValuation (originalCubicScheme n).functionField (WithTop ℤ) :=
  ActualDvrMeromorphicOrder318.value (InfinityStalk n) (originalCubicScheme n).functionField

/-- The original pole has order MINUS two, for every root parameter a.
The actual unit quotient is retained before taking the valuation. -/
theorem named_root (n a : K) :
    value n (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a) = (-2 : WithTop ℤ) := by
  obtain ⟨e,d,hd⟩ := ActualTwoDescentOriginalInfinityStalkPoleRebuild318.fraction n a
  rw [hd,(value n).map_div,(value n).map_div,(value n).map_pow]
  change ActualDvrMeromorphicOrder318.value (InfinityStalk n) _ _ -
    ActualDvrMeromorphicOrder318.value (InfinityStalk n) _ _ -
    2 • ActualDvrMeromorphicOrder318.value (InfinityStalk n) _ _ = _
  rw [ActualDvrMeromorphicOrder318.value_unit _ _ _ d.isUnit,
    ActualDvrMeromorphicOrder318.value_unit _ _ _ e.isUnit,
    ActualDvrMeromorphicOrder318.value_uniformizer _ _ _
      (ActualTwoDescentOriginalStalkFactorsRebuild318.infinity_uniformizer n)]
  norm_num

theorem integral_order (n a : K) :
    ActualDvrMeromorphicOrder318.order (InfinityStalk n) (originalCubicScheme n).functionField
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a) = -2 :=
  ActualDvrMeromorphicOrder318.order_eq _ _ _ (-2) (named_root n a)
end ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318
''',
'ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318':'''module
public import ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- At EVERY off-support scheme point the actual stalk unit is produced.
If its stalk is a DVR, its normalized valuation is therefore zero. The
DVR premise here is explicit, not silently deduced for all scheme points. -/
theorem value_zero (n : K) (i : Fin 3) (p : originalCubicScheme n)
    [IsDiscreteValuationRing ((originalCubicScheme n).presheaf.stalk p)]
    (hr : p ≠ rootPoint n i) (ho : p ≠ infinityPoint n) :
    ActualDvrMeromorphicOrder318.value ((originalCubicScheme n).presheaf.stalk p)
      (originalCubicScheme n).functionField
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i)) = 0 := by
  obtain ⟨s,hs,hf⟩ := ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318.unit n i p hr ho
  rw [←hf]
  exact ActualDvrMeromorphicOrder318.value_unit _ _ s hs

/-- The inverse uses the SAME actual stalk embedding, including at
non-rational points. No finite test of closed points is substituted. -/
theorem inverse_unit (n : K) (i : Fin 3) (p : originalCubicScheme n)
    (hr : p ≠ rootPoint n i) (ho : p ≠ infinityPoint n) :
    ∃ s : ((originalCubicScheme n).presheaf.stalk p)ˣ,
      algebraMap ((originalCubicScheme n).presheaf.stalk p) (originalCubicScheme n).functionField
        (s : (originalCubicScheme n).presheaf.stalk p) =
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ := by
  obtain ⟨s,hs,hf⟩ := ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318.unit n i p hr ho
  obtain ⟨u,hu⟩ := hs
  refine ⟨u⁻¹, ?_⟩
  rw [map_units_inv,hu,hf]
end ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318
''',
'ActualTwoDescentOriginalPrincipalRootCertificateRebuild318':'''module
public import ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalPrincipalRootCertificateRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Concrete principal-function certificate on the actual original
scheme. This is deliberately not named a general principal-divisor map. -/
structure Certificate (n : K) (i : Fin 3) [Fact (n ≠ 0)] where
  function : (originalCubicScheme n).functionField
  same_function : function = ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
    (ActualTwoDescentOriginalRootIdeals318.root n i)
  nonzero : function ≠ 0
  root_order : ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.value n i function = 2
  infinity_order : ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.value n function = -2
  off_support : ∀ p : originalCubicScheme n, p ≠ rootPoint n i → p ≠ infinityPoint n →
    ∃ s : (originalCubicScheme n).presheaf.stalk p,
      IsUnit s ∧ algebraMap ((originalCubicScheme n).presheaf.stalk p)
        (originalCubicScheme n).functionField s = function

/-- Every input is produced for the SAME n, root index, scheme, field,
and coefficient embedding. n≠0 remains on the marked root DVR. -/
def certificate (n : K) (i : Fin 3) [Fact (n ≠ 0)] : Certificate n i where
  function := ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
    (ActualTwoDescentOriginalRootIdeals318.root n i)
  same_function := rfl
  nonzero := ActualTwoDescentOriginalAllPointRootSupportRebuild318.nonzero n i
  root_order := ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.named_root n i
  infinity_order := ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.named_root n _
  off_support := ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318.unit n i
end ActualTwoDescentOriginalPrincipalRootCertificateRebuild318
''',
'ActualTwoDescentOriginalPrincipalInverseCertificateRebuild318':'''module
public import ActualTwoDescentOriginalPrincipalRootCertificateRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalPrincipalInverseCertificateRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Exact opposite sign for the inverse function. This distinguishes
O(O-Ta) and O(Ta-O) before any associated-sheaf comparison. -/
theorem root_order (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.value n i
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ = (-2 : WithTop ℤ) := by
  rw [(ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.value n i).map_inv,
    ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.named_root]
  norm_num

theorem infinity_order (n a : K) :
    ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.value n
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a)⁻¹ = (2 : WithTop ℤ) := by
  rw [(ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.value n).map_inv,
    ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.named_root]
  norm_num

/-- A combined actual inverse certificate, with all off-support points
and actual stalk embeddings rather than selected geometric points. -/
theorem all_points (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.value n i
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ = -2 ∧
    ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.value n
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ = 2 ∧
    ∀ p : originalCubicScheme n, p ≠ rootPoint n i → p ≠ infinityPoint n →
      ∃ s : ((originalCubicScheme n).presheaf.stalk p)ˣ,
        algebraMap ((originalCubicScheme n).presheaf.stalk p) (originalCubicScheme n).functionField
          (s : (originalCubicScheme n).presheaf.stalk p) =
        (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
          (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ :=
  ⟨root_order n i,infinity_order n _,
    ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318.inverse_unit n i⟩
end ActualTwoDescentOriginalPrincipalInverseCertificateRebuild318
'''}
for name,s in sources.items():(p/(name+'.lean')).write_text(s)
print(p, len(sources),sum(len(s.splitlines()) for s in sources.values()))
