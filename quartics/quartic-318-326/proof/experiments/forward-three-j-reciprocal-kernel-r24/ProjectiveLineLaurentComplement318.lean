module
public import ThreeJFiniteLaurentMap318
public import Mathlib.RingTheory.PrincipalIdealDomain
public section
noncomputable section
namespace ProjectiveLineLaurentComplement318
open AlgebraicGeometry CategoryTheory Polynomial
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The complement of the punctured affine line is a single scheme point,
proved at the level of prime ideals over Q, not only complex-valued points. -/
lemma affine_origin_finite :
    Set.Finite {p : PrimeSpectrum ℚ[X] | (X:ℚ[X]) ∈ p.asIdeal} := by
  have hm : (Ideal.span {(X:ℚ[X])}).IsMaximal := by
    simpa only [C_0,sub_zero] using
      PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C (0:ℚ))
  have he (p : PrimeSpectrum ℚ[X]) (hp : (X:ℚ[X]) ∈ p.asIdeal) :
      Ideal.span {(X:ℚ[X])}=p.asIdeal := by
    apply hm.eq_of_le p.isPrime.ne_top
    exact Ideal.span_le.mpr (by rintro x rfl; exact hp)
  apply Set.Subsingleton.finite
  intro p hp q hq
  apply PrimeSpectrum.ext
  exact (he p hp).symm.trans (he q hq)

lemma chart_mem_laurent (i : Fin 2) (p : PrimeSpectrum ℚ[X])
    (hp : (X:ℚ[X]) ∉ p.asIdeal) :
    JLineAtlas318.chart ℚ i p ∈ ProjectiveLineOverlap318.embedding.opensRange := by
  rw [←ProjectiveLineOverlap318.full_intersection]
  fin_cases i
  · refine ⟨?_,⟨p,rfl⟩⟩
    change p ∈ JLineAtlas318.chart ℚ 0 ⁻¹ᵁ (JLineAtlas318.chart ℚ 1).opensRange
    rw [ProjectiveLinePointEquiv318.chart_zero_preimage_one]
    exact hp
  · refine ⟨⟨p,rfl⟩,?_⟩
    change p ∈ JLineAtlas318.chart ℚ 1 ⁻¹ᵁ (JLineAtlas318.chart ℚ 0).opensRange
    have he := ProjectiveLineOverlap318.chart_one_preimage_zero
    rw [Scheme.Hom.image_top_eq_opensRange] at he
    rw [he]
    exact hp

/-- The exact original Laurent source open has finite complement in the
entire original projective scheme, including every non-complex scheme point. -/
theorem complement_finite :
    Set.Finite ((Set.range ProjectiveLineOverlap318.embedding)ᶜ) := by
  let B : Set (PrimeSpectrum ℚ[X]) := {p | (X:ℚ[X]) ∈ p.asIdeal}
  have hB : B.Finite := affine_origin_finite
  apply ((hB.image (JLineAtlas318.chart ℚ 0)).union
    (hB.image (JLineAtlas318.chart ℚ 1))).subset
  intro p hp
  have htop : p ∈ (⊤ : (ProjectiveJLine318.scheme ℚ).Opens) := trivial
  rw [←JLineAtlas318.standard_opens_cover ℚ,TopologicalSpace.Opens.mem_iSup] at htop
  obtain ⟨i,hi⟩ := htop
  rw [←JLineAtlas318.chart_range] at hi
  obtain ⟨q,rfl⟩ := hi
  have hq : q ∈ B := by
    by_contra hn
    exact hp (chart_mem_laurent i q hn)
  fin_cases i
  · exact Or.inl ⟨q,hq,rfl⟩
  · exact Or.inr ⟨q,hq,rfl⟩

end ProjectiveLineLaurentComplement318
