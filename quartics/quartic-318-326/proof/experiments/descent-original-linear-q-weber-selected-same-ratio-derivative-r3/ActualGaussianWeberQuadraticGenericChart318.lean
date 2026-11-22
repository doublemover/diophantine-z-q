module
public import ActualGaussianWeberRationalNoDegreeRise318
public import Mathlib.RingTheory.AdjoinRoot
public section
noncomputable section

namespace ActualGaussianWeberQuadraticGenericChart318

open IsLocalRing Polynomial
open ActualGaussianWeberRationalNoDegreeRise318 ActualGaussianWeberPrimitiveRational318

/-- The literal original affine coordinate ring:
the outer indeterminate is Y; the indeterminate inside R[X] is x. -/
@[expose] def relation (R : Type*) [CommRing R] : (R[X])[X] :=
  X^2 - C ((X:R[X])^3-X)

abbrev Chart (R : Type*) [CommRing R] := AdjoinRoot (relation R)

private theorem rel_monic (R : Type*) [CommRing R] : (relation R).Monic :=
  monic_X_pow_sub_C _ (by decide)

private theorem rel_degree (R : Type*) [CommRing R] [Nontrivial R] :
    (relation R).degree=2 := degree_X_pow_sub_C (by decide : 0<2) _

private theorem rel_natDegree (R : Type*) [CommRing R] [Nontrivial R] :
    (relation R).natDegree=2 := natDegree_X_pow_sub_C

private theorem rel_map {R S : Type*} [CommRing R] [CommRing S] (f : R→+*S) :
    (relation R).map (Polynomial.mapRingHom f)=relation S := by
  simp only [relation,Polynomial.map_sub,Polynomial.map_pow,map_X,map_C,coe_mapRingHom]

@[expose] def mapChart {R S : Type*} [CommRing R] [CommRing S] (f : R→+*S) :
    Chart R→+*Chart S :=
  AdjoinRoot.map (Polynomial.mapRingHom f) (relation R) (relation S)
    (by rw [rel_map f] <;> exact dvd_rfl)

@[expose] def element {R : Type*} [CommRing R] (a b : R[X]) : Chart R :=
  AdjoinRoot.of (relation R) a + AdjoinRoot.of (relation R) b * AdjoinRoot.root (relation R)

private def linearPolynomial {T : Type*} [CommRing T] (a b : T) : T[X] :=
  C a + monomial 1 b

private theorem element_mk {R : Type*} [CommRing R] (a b : R[X]) :
    element a b=AdjoinRoot.mk (relation R) (linearPolynomial a b) := by
  simp only [element,linearPolynomial,←C_mul_X_pow_eq_monomial,pow_one,
    map_add,map_mul,AdjoinRoot.mk_C,AdjoinRoot.mk_X]

private theorem linear_degree {T : Type*} [CommRing T] (a b : T) :
    (linearPolynomial a b).natDegree≤1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h0 : n≠0 := by omega
  have h1 : 1≠n := by omega
  simp [linearPolynomial,coeff_C,coeff_monomial,h0,h0.symm,h1]

private theorem linear_eq {T : Type*} [CommRing T] (q : T[X]) (h : q.natDegree<2) :
    linearPolynomial (q.coeff 0) (q.coeff 1)=q := by
  ext n
  by_cases h0 : n=0
  · subst n
    simp [linearPolynomial,coeff_C,coeff_monomial]
  by_cases h1 : n=1
  · subst n
    simp [linearPolynomial,coeff_C,coeff_monomial]
  have hn : q.natDegree<n := by omega
  have h10 : 1 ≠ n := fun e => h1 e.symm
  simp [linearPolynomial,coeff_C,coeff_monomial,h0,h10,coeff_eq_zero_of_natDegree_lt hn]

theorem element_coefficients {R : Type*} [CommRing R] [Nontrivial R] {a b c d : R[X]}
    (h : (element a b : Chart R)=element c d) : a=c ∧ b=d := by
  rw [element_mk,element_mk] at h
  have get (a b : R[X]) :
      (linearPolynomial a b) %ₘ relation R = linearPolynomial a b := by
    apply (modByMonic_eq_self_iff (rel_monic R)).mpr
    rw [rel_degree]
    have hn : (linearPolynomial a b).natDegree<2 := (linear_degree a b).trans_lt (by decide)
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hn)
  have he := congrArg (AdjoinRoot.modByMonicHom (rel_monic R)) h
  simp only [AdjoinRoot.modByMonicHom_mk,get] at he
  constructor
  · simpa [linearPolynomial,coeff_C,coeff_monomial] using
      congrArg (fun q : (R[X])[X] => q.coeff 0) he
  · simpa [linearPolynomial,coeff_C,coeff_monomial] using
      congrArg (fun q : (R[X])[X] => q.coeff 1) he

theorem element_surjective {R : Type*} [CommRing R] [Nontrivial R] (z : Chart R) :
    ∃ a b : R[X], element a b=z := by
  obtain ⟨u,hu⟩ := AdjoinRoot.mk_surjective (g:=relation R) z
  let q := u %ₘ relation R
  have h1 : relation R≠1 := by
    intro h
    have H := rel_natDegree R
    rw [h,natDegree_one] at H
    omega
  have hq : q.natDegree<2 := by
    rw [←rel_natDegree R]
    exact natDegree_modByMonic_lt u (rel_monic R) h1
  refine ⟨q.coeff 0,q.coeff 1,?_⟩
  rw [element_mk,linear_eq q hq]
  rw [←hu]
  have hMk : AdjoinRoot.mk (relation R)
      (AdjoinRoot.modByMonicHom (rel_monic R) (AdjoinRoot.mk (relation R) u)) =
      AdjoinRoot.mk (relation R) u :=
    AdjoinRoot.mk_leftInverse (rel_monic R) (AdjoinRoot.mk (relation R) u)
  rw [AdjoinRoot.modByMonicHom_mk] at hMk
  exact hMk

theorem element_map {R S : Type*} [CommRing R] [CommRing S] (f : R→+*S) (a b : R[X]) :
    mapChart f (element a b)=element (a.map f) (b.map f) := by
  simp only [element,mapChart,map_add,map_mul,AdjoinRoot.map_of,AdjoinRoot.map_root,coe_mapRingHom]

theorem mul_element {R : Type*} [CommRing R] (s a b : R[X]) :
    AdjoinRoot.of (relation R) s * element a b=element (s*a) (s*b) := by
  simp only [element,map_mul,mul_add,mul_assoc]

variable {K : Type*} [Field K] (V : ValuationSubring K)

/-- A pair of actual integral functions in the literal quadratic
coordinate ring supplies the finite presentation used in no-degree-rise.
The literal C₁/D₁ is finite at the generic residue point if the actual reduced
denominator in the quadratic coordinate ring is nonzero. -/
theorem finite_presentation_of_chart {A B : K[X]} (C₁ D₁ : Chart V)
    (hD : mapChart (residue V) D₁ ≠ 0)
    (h : AdjoinRoot.of (relation K) A * mapChart V.subtype D₁ =
        AdjoinRoot.of (relation K) B * mapChart V.subtype C₁) :
    Nonempty (FinitePresentation V A B) := by
  obtain ⟨c₀,c₁,hc⟩ := element_surjective C₁
  obtain ⟨d₀,d₁,hd⟩ := element_surjective D₁
  rw [←hd,←hc,element_map,element_map,mul_element,mul_element] at h
  have hh := element_coefficients h
  refine ⟨⟨c₀,c₁,d₀,d₁,hh.1,hh.2,?_⟩⟩
  by_contra H
  push_neg at H
  exact hD (by rw [←hd,element_map,H.1,H.2]; simp [element])

private theorem chart_reduced_cross {A B : K[X]} (T : PrimitivePair V A B)
    (C₁ D₁ : Chart V)
    (h : AdjoinRoot.of (relation K) A * mapChart V.subtype D₁ =
        AdjoinRoot.of (relation K) B * mapChart V.subtype C₁) :
    AdjoinRoot.of (relation (ResidueField V)) (T.num.map (residue V)) * mapChart (residue V) D₁ =
    AdjoinRoot.of (relation (ResidueField V)) (T.den.map (residue V)) * mapChart (residue V) C₁ := by
  obtain ⟨c₀,c₁,hc⟩ := element_surjective C₁
  obtain ⟨d₀,d₁,hd⟩ := element_surjective D₁
  rw [←hd,←hc,element_map,element_map,mul_element,mul_element] at h ⊢
  have e := element_coefficients h
  rw [reduced_cross V T c₀ d₀ e.1,reduced_cross V T c₁ d₁ e.2]

/-- On the literal Weber generic chart, a finite local presentation
can be replaced by a purely rational x-presentation with nonzero
reduced denominator and no degree rise. The output equality is in the
actual reduced quadratic coordinate ring, before any cancellation.
The bound N is supplied by the generic characteristic-zero coordinate
calculation, not inferred from the special fibre. -/
theorem specialize_actual_chart (A B : K[X]) (hB : B≠0) (N : ℕ)
    (hAdeg : A.natDegree≤N) (hBdeg : B.natDegree≤N)
    (C₁ D₁ : Chart V)
    (hD : mapChart (residue V) D₁ ≠ 0)
    (h : AdjoinRoot.of (relation K) A * mapChart V.subtype D₁ =
        AdjoinRoot.of (relation K) B * mapChart V.subtype C₁) :
    ∃ T : PrimitivePair V A B,
      T.den.map (residue V) ≠ 0 ∧
      (T.num.map (residue V)).natDegree≤N ∧ (T.den.map (residue V)).natDegree≤N ∧
      RatFunc.mk (T.num.map V.subtype) (T.den.map V.subtype)=RatFunc.mk A B ∧
      AdjoinRoot.of (relation (ResidueField V)) (T.num.map (residue V)) * mapChart (residue V) D₁ =
      AdjoinRoot.of (relation (ResidueField V)) (T.den.map (residue V)) * mapChart (residue V) C₁ := by
  obtain ⟨G⟩ := finite_presentation_of_chart V C₁ D₁ hD h
  obtain ⟨T,hden,hn,hd,hgen,_⟩ := specialize_without_degree_rise V A B hB G
  exact ⟨T,hden,hn.trans hAdeg,hd.trans hBdeg,hgen,chart_reduced_cross V T C₁ D₁ h⟩

end ActualGaussianWeberQuadraticGenericChart318
