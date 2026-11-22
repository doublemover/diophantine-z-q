module
public import ActualGaussianWeberGenericChartDomain318
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public section
noncomputable section

namespace ActualGaussianWeberGaussLocalization318

open IsLocalRing Polynomial
open ActualGaussianWeberPrimitiveRational318 ActualGaussianWeberQuadraticGenericChart318
open ActualGaussianWeberGenericChartDomain318

variable {K : Type*} [Field K] (V : ValuationSubring K)

instance chartFieldDomain (L : Type*) [Field L] : IsDomain (Chart L) := chart_isDomain L

abbrev FunctionField (L : Type*) [Field L] := FractionRing (Chart L)

@[expose] def prime : Ideal (Chart V) := RingHom.ker (mapChart (residue V))

instance prime_isPrime : (prime V).IsPrime := RingHom.ker_isPrime _

abbrev Local := Localization.AtPrime (prime V)

theorem denominator_reduces {d : Chart V} (hd : d ∈ (prime V).primeCompl) :
    mapChart (residue V) d≠0 := by
  intro h
  exact (Ideal.mem_primeCompl_iff.mp hd) ((RingHom.mem_ker (f:=mapChart (residue V))).mpr h)

/-- The two actual maps on the chart, into its generic and residue
function fields. Their denominators come from the same prime complement. -/
@[expose] def genericBase : Chart V→+*FunctionField K :=
  (algebraMap (Chart K) (FunctionField K)).comp (mapChart V.subtype)

@[expose] def residueBase : Chart V→+*FunctionField (ResidueField V) :=
  (algebraMap (Chart (ResidueField V)) (FunctionField (ResidueField V))).comp
    (mapChart (residue V))

theorem genericBase_injective : Function.Injective (genericBase V) :=
  (IsFractionRing.injective (Chart K) (FunctionField K)).comp
    (mapChart_injective V.subtype V.subtype_injective)

theorem genericUnit (d : (prime V).primeCompl) : IsUnit (genericBase V d) := by
  apply isUnit_iff_ne_zero.mpr
  intro hd
  have e : (d:Chart V)=0 :=
    genericBase_injective V (hd.trans (map_zero (genericBase V)).symm)
  apply denominator_reduces V d.property
  rw [e,map_zero]

theorem residueUnit (d : (prime V).primeCompl) : IsUnit (residueBase V d) := by
  apply isUnit_iff_ne_zero.mpr
  intro hd
  apply denominator_reduces V d.property
  exact IsFractionRing.injective (Chart (ResidueField V)) (FunctionField (ResidueField V))
    (hd.trans (map_zero _).symm)

@[expose] def intoGeneric : Local V→+*FunctionField K :=
  IsLocalization.lift (genericUnit V)

@[expose] def intoResidue : Local V→+*FunctionField (ResidueField V) :=
  IsLocalization.lift (residueUnit V)

theorem intoGeneric_algebraMap (a : Chart V) :
    intoGeneric V (algebraMap (Chart V) (Local V) a)=genericBase V a :=
  IsLocalization.lift_eq (genericUnit V) a

theorem intoResidue_algebraMap (a : Chart V) :
    intoResidue V (algebraMap (Chart V) (Local V) a)=residueBase V a :=
  IsLocalization.lift_eq (residueUnit V) a

theorem intoGeneric_fraction (a : Chart V) (d : (prime V).primeCompl) :
    intoGeneric V (IsLocalization.mk' (Local V) a d)=genericBase V a/genericBase V d := by
  apply (eq_div_iff (genericUnit V d).ne_zero).2
  have e := congrArg (intoGeneric V) (IsLocalization.mk'_spec (Local V) a d)
  simpa only [map_mul,intoGeneric_algebraMap] using e

theorem intoResidue_fraction (a : Chart V) (d : (prime V).primeCompl) :
    intoResidue V (IsLocalization.mk' (Local V) a d)=residueBase V a/residueBase V d := by
  apply (eq_div_iff (residueUnit V d).ne_zero).2
  have e := congrArg (intoResidue V) (IsLocalization.mk'_spec (Local V) a d)
  simpa only [map_mul,intoResidue_algebraMap] using e

theorem intoGeneric_injective : Function.Injective (intoGeneric V) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (prime V).primeCompl (intoGeneric V)).mpr
  intro a b
  simp only [intoGeneric_algebraMap]
  constructor
  · intro h
    simpa only [intoGeneric_algebraMap] using congrArg (intoGeneric V) h
  · intro h
    rw [genericBase_injective V h]

theorem intoResidue_surjective : Function.Surjective (intoResidue V) := by
  intro z
  obtain ⟨a,b,hb,hz⟩ := IsFractionRing.div_surjective (Chart (ResidueField V)) z
  obtain ⟨a₀,ha⟩ := mapChart_surjective (residue V) residue_surjective a
  obtain ⟨b₀,he⟩ := mapChart_surjective (residue V) residue_surjective b
  let d : (prime V).primeCompl := ⟨b₀,(Ideal.mem_primeCompl_iff).mpr (by
    intro H
    have h : mapChart (residue V) b₀=0 := (RingHom.mem_ker (f:=mapChart (residue V))).mp H
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) (he.symm.trans h))⟩
  refine ⟨IsLocalization.mk' (Local V) a₀ d,?_⟩
  rw [intoResidue_fraction,residueBase,RingHom.comp_apply,RingHom.comp_apply]
  change algebraMap (Chart (ResidueField V)) _ (mapChart (residue V) a₀) /
    algebraMap (Chart (ResidueField V)) _ (mapChart (residue V) b₀) = z
  rw [ha,he]
  exact hz

instance intoResidue_isLocal : IsLocalHom (intoResidue V) :=
  IsLocalHom.of_surjective _ (intoResidue_surjective V)

/-- Unlike a closed point, the Gauss prime is only prime. Its actual
residue field is the function field of the residue curve. -/
@[expose] def residueFunctionField :
    ResidueField (Local V) ≃+* FunctionField (ResidueField V) :=
  RingEquiv.ofBijective (ResidueField.lift (intoResidue V)) (by
    constructor
    · exact (ResidueField.lift (intoResidue V)).injective
    · intro z
      obtain ⟨w,hw⟩ := intoResidue_surjective V z
      exact ⟨residue (Local V) w,(ResidueField.lift_residue_apply _ _).trans hw⟩)

theorem residueFunctionField_apply (z : Local V) :
    residueFunctionField V (residue (Local V) z)=intoResidue V z := by
  change ResidueField.lift (intoResidue V) (residue (Local V) z)=intoResidue V z
  exact ResidueField.lift_residue_apply _ _

private theorem inclusion_nonzero {L : Type*} [Field L] {A : L[X]} (hA : A≠0) :
    algebraMap (Chart L) (FunctionField L) (AdjoinRoot.of (relation L) A)≠0 := by
  have hm : (relation L).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : 0 < (relation L).degree := by
    rw [show (relation L).degree=2 from degree_X_pow_sub_C (by decide : 0<2) _]
    decide
  let e := (IsFractionRing.injective (Chart L) (FunctionField L)).comp
    (AdjoinRoot.of.injective_of_monic_of_degree_pos hm hdeg)
  intro h
  exact hA (e (h.trans (map_zero _).symm))

/-- If the literal generic x-coordinate is finite in the actual
Gauss localization, the reduced function-field value has an x-rational
presentation of no larger degree. The local lift supplies the genuine
integral numerator/denominator, so callers no longer supply C,D or an
ad hoc residual equality. -/
theorem specialize_local_rational_coordinate (A B : K[X]) (hB : B≠0) (N : ℕ)
    (hAdeg : A.natDegree≤N) (hBdeg : B.natDegree≤N) (z : Local V)
    (hz : intoGeneric V z=
      algebraMap (Chart K) (FunctionField K) (AdjoinRoot.of (relation K) A) /
      algebraMap (Chart K) (FunctionField K) (AdjoinRoot.of (relation K) B)) :
    ∃ T : PrimitivePair V A B, T.den.map (residue V)≠0 ∧
      (T.num.map (residue V)).natDegree≤N ∧ (T.den.map (residue V)).natDegree≤N ∧
      intoResidue V z=
        algebraMap (Chart (ResidueField V)) (FunctionField (ResidueField V))
          (AdjoinRoot.of (relation (ResidueField V)) (T.num.map (residue V))) /
        algebraMap (Chart (ResidueField V)) (FunctionField (ResidueField V))
          (AdjoinRoot.of (relation (ResidueField V)) (T.den.map (residue V))) := by
  obtain ⟨c,d,rfl⟩ := IsLocalization.exists_mk'_eq (prime V).primeCompl z
  rw [intoGeneric_fraction V] at hz
  have h := (div_eq_div_iff (genericUnit V d).ne_zero (inclusion_nonzero hB)).mp hz
  have hcross : AdjoinRoot.of (relation K) A * mapChart V.subtype (d:Chart V) =
      AdjoinRoot.of (relation K) B * mapChart V.subtype c := by
    apply IsFractionRing.injective (Chart K) (FunctionField K)
    simpa only [genericBase,RingHom.comp_apply,map_mul,mul_comm] using h.symm
  obtain ⟨T,hn,hA,hB',_,e⟩ :=
    specialize_actual_chart V A B hB N hAdeg hBdeg c (d:Chart V)
      (denominator_reduces V d.property) hcross
  refine ⟨T,hn,hA,hB',?_⟩
  rw [intoResidue_fraction V]
  apply (div_eq_div_iff (residueUnit V d).ne_zero (inclusion_nonzero hn)).2
  simpa only [residueBase,RingHom.comp_apply,map_mul,mul_comm] using
    congrArg (algebraMap (Chart (ResidueField V)) (FunctionField (ResidueField V))) e.symm

end ActualGaussianWeberGaussLocalization318
