module
public import ActualGaussianWeberGaussLocalization318
public section
noncomputable section

namespace ActualGaussianWeberGaussValuation318

open IsLocalRing Polynomial
open ActualGaussianWeberPrimitiveRational318 ActualGaussianWeberQuadraticGenericChart318
open ActualGaussianWeberGaussLocalization318

variable {K : Type*} [Field K] (V : ValuationSubring K)

private theorem element_zero (R : Type*) [CommRing R] :
    (element (0:R[X]) 0 : Chart R)=0 := by simp [element]

/-- Simultaneous integral representatives of the two literal generic
curve functions, using a common scalar for all four polynomial
coefficients, not a distinct scale per curve coordinate. -/
theorem primitive_chart_pair (A B : Chart K) (hB : B≠0) :
    ∃ (d : K) (a b : Chart V), d≠0 ∧
      AdjoinRoot.of (relation K) (C d) * mapChart V.subtype a=A ∧
      AdjoinRoot.of (relation K) (C d) * mapChart V.subtype b=B ∧
      (mapChart (residue V) a≠0 ∨ mapChart (residue V) b≠0) := by
  obtain ⟨A₀,A₁,hA⟩ := element_surjective A
  obtain ⟨B₀,B₁,hBs⟩ := element_surjective B
  let P : Bool×Bool → K[X] := fun t =>
    if t.1 then (if t.2 then B₁ else B₀) else (if t.2 then A₁ else A₀)
  have hP : ∃ i, P i≠0 := by
    by_contra! H
    have h0 : B₀=0 := H (true,false)
    have h1 : B₁=0 := H (true,true)
    apply hB
    rw [←hBs,h0,h1,element_zero K]
  obtain ⟨d,Q,hd,hQ,_,i,hi⟩ := primitive_family V P hP
  let a := element (Q (false,false)) (Q (false,true))
  let b := element (Q (true,false)) (Q (true,true))
  have ea₀ : C d*(Q (false,false)).map V.subtype=A₀ := hQ (false,false)
  have ea₁ : C d*(Q (false,true)).map V.subtype=A₁ := hQ (false,true)
  have eb₀ : C d*(Q (true,false)).map V.subtype=B₀ := hQ (true,false)
  have eb₁ : C d*(Q (true,true)).map V.subtype=B₁ := hQ (true,true)
  refine ⟨d,a,b,hd,?_,?_,?_⟩
  · change AdjoinRoot.of (relation K) (C d) *
      mapChart V.subtype (element (Q (false,false)) (Q (false,true))) = A
    rw [element_map,mul_element,ea₀,ea₁,hA]
  · change AdjoinRoot.of (relation K) (C d) *
      mapChart V.subtype (element (Q (true,false)) (Q (true,true))) = B
    rw [element_map,mul_element,eb₀,eb₁,hBs]
  · by_contra! H
    have ha := H.1
    have hb := H.2
    change mapChart (residue V) (element (Q (false,false)) (Q (false,true))) = 0 at ha
    change mapChart (residue V) (element (Q (true,false)) (Q (true,true))) = 0 at hb
    rw [element_map,←element_zero (ResidueField V)] at ha
    rw [element_map,←element_zero (ResidueField V)] at hb
    obtain ⟨ha₀,ha₁⟩ := element_coefficients ha
    obtain ⟨hb₀,hb₁⟩ := element_coefficients hb
    apply hi
    rcases i with ⟨x,y⟩
    cases x <;> cases y
    · exact ha₀
    · exact ha₁
    · exact hb₀
    · exact hb₁

private theorem fraction_of_primitive (f : FunctionField K) :
    ∃ a b : Chart V, f=genericBase V a/genericBase V b ∧
      (mapChart (residue V) a≠0 ∨ mapChart (residue V) b≠0) := by
  obtain ⟨A,B,hB,hF⟩ := IsFractionRing.div_surjective (Chart K) f
  obtain ⟨d,a,b,hd,ea,eb,hfin⟩ := primitive_chart_pair V A B
    (mem_nonZeroDivisors_iff_ne_zero.mp hB)
  let E := algebraMap (Chart K) (FunctionField K)
  have hm : (relation K).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : (0 : WithBot ℕ) < (relation K).degree := by
    rw [show (relation K).degree=2 from degree_X_pow_sub_C (by decide : 0<2) _]
    decide
  have hInj := (IsFractionRing.injective (Chart K) (FunctionField K)).comp
    (AdjoinRoot.of.injective_of_monic_of_degree_pos hm hdeg)
  have hv : E (AdjoinRoot.of (relation K) (C d))≠0 := by
    intro h
    exact C_ne_zero.mpr hd
      (hInj (h.trans (map_zero (E.comp (AdjoinRoot.of (relation K)))).symm))
  have eA : E A=E (AdjoinRoot.of (relation K) (C d))*genericBase V a := by
    simpa only [E,map_mul,genericBase,RingHom.comp_apply] using (congrArg E ea).symm
  have eB : E B=E (AdjoinRoot.of (relation K) (C d))*genericBase V b := by
    simpa only [E,map_mul,genericBase,RingHom.comp_apply] using (congrArg E eb).symm
  refine ⟨a,b,?_,hfin⟩
  rw [←hF,eA,eB,mul_div_mul_left _ _ hv]

private theorem enters_range (a b : Chart V) (hb : mapChart (residue V) b≠0) :
    genericBase V a/genericBase V b ∈ (intoGeneric V).range := by
  let d : (prime V).primeCompl := ⟨b,Ideal.mem_primeCompl_iff.mpr
    (fun e => hb ((RingHom.mem_ker (f:=mapChart (residue V))).mp e))⟩
  refine ⟨IsLocalization.mk' (Local V) a d,?_⟩
  exact intoGeneric_fraction V a d

theorem generic_mem_or_inv_mem (f : FunctionField K) :
    f ∈ (intoGeneric V).range ∨ f⁻¹ ∈ (intoGeneric V).range := by
  obtain ⟨a,b,h,hf⟩ := fraction_of_primitive V f
  rcases hf with ha|hb
  · right
    rw [h,inv_div]
    exact enters_range V b a ha
  · exact Or.inl (h.symm ▸ enters_range V a b hb)

/-- The actual selected curve Gauss place as a valuation subring of
the same generic function field. Its underlying subring is exactly
the image of localization at the true reduction prime. -/
@[expose] def gauss : ValuationSubring (FunctionField K) :=
  ValuationSubring.ofSubring (intoGeneric V).range (generic_mem_or_inv_mem V)

/-- Every integral generic function has an actual lift to the local
chart, now with no assumed finite numerator-denominator dictionary. -/
theorem exists_local_of_mem (f : FunctionField K) (hf : f ∈ gauss V) :
    ∃ z : Local V, intoGeneric V z=f := by
  change f ∈ (intoGeneric V).range at hf
  exact hf

/-- The actual embedded valuation subring is exactly the prime
localization, with no completion or other point chosen. -/
@[expose] def localEquiv : Local V ≃+* gauss V :=
  RingEquiv.ofBijective (intoGeneric V).rangeRestrict (by
    constructor
    · intro a b h
      exact intoGeneric_injective V (congrArg Subtype.val h)
    · intro y
      obtain ⟨z,hz⟩ := exists_local_of_mem V (y:FunctionField K) y.property
      exact ⟨z,Subtype.ext hz⟩)

@[expose] def gaussResidue : ResidueField (gauss V) ≃+* FunctionField (ResidueField V) :=
  (ResidueField.mapEquiv (localEquiv V).symm).trans (residueFunctionField V)

theorem gauss_residue_of_local (z : Local V) :
    gaussResidue V (residue (gauss V) (localEquiv V z))=intoResidue V z := by
  change (residueFunctionField V) (ResidueField.mapEquiv (localEquiv V).symm
    (residue (gauss V) (localEquiv V z)))=intoResidue V z
  rw [ResidueField.mapEquiv_apply,ResidueField.map_residue]
  change residueFunctionField V (residue (Local V) ((localEquiv V).symm ((localEquiv V) z))) =
    intoResidue V z
  rw [RingEquiv.symm_apply_apply,residueFunctionField_apply]

@[expose] def integralChart : Chart V →+* gauss V :=
  (localEquiv V).toRingHom.comp (algebraMap (Chart V) (Local V))

theorem integral_chart_specialize (c : Chart V) :
    gaussResidue V (residue (gauss V) (integralChart V c))=residueBase V c := by
  change gaussResidue V (residue (gauss V) (localEquiv V (algebraMap _ _ c)))=_
  rw [gauss_residue_of_local,intoResidue_algebraMap]

end ActualGaussianWeberGaussValuation318
