module
public import InfinityGlobalBase318
public section
noncomputable section
namespace ContactSmoothBaseCover318
open CategoryTheory AlgebraicGeometry Polynomial
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev R:=ℚ[X]
abbrev Punctured:=Localization.Away (X:R)
@[expose] def xUnit : Puncturedˣ:=
  (IsLocalization.Away.algebraMap_isUnit (X:R)).unit
lemma xUnit_coe : (xUnit:Punctured)=algebraMap R Punctured X:=
  (IsLocalization.Away.algebraMap_isUnit (X:R)).unit_spec

lemma punctured_overlap :
    Spec.map (CommRingCat.ofHom (algebraMap R Punctured))≫JLineAtlas318.chart ℚ 0=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (↑xUnit⁻¹:Punctured)).toRingHom)≫
      JLineAtlas318.chart ℚ 1:=by
  have e:=JLineOverlap318.unit_chart_overlap (R:=ℚ) xUnit⁻¹
  simp only [inv_inv] at e
  have he:(Polynomial.aeval (↑xUnit:Punctured)).toRingHom=algebraMap R Punctured:=by
    apply Polynomial.ringHom_ext
    · intro q
      simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C]
      exact IsScalarTower.algebraMap_apply ℚ R Punctured q
    · simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X] using xUnit_coe
  rw [he] at e
  exact e.symm

lemma chart0_X_in_chart1 (p:Spec (CommRingCat.of R))
    (hp:p∈PrimeSpectrum.basicOpen (X:R)) :
    JLineAtlas318.chart ℚ 0 p∈(JLineAtlas318.chart ℚ 1).opensRange:=by
  obtain ⟨q,rfl⟩:=(Set.ext_iff.mp
    (PrimeSpectrum.localization_away_comap_range Punctured (X:R)) p).mpr hp
  refine ⟨(Spec.map (CommRingCat.ofHom
    (Polynomial.aeval (↑xUnit⁻¹:Punctured)).toRingHom) :
      Spec (CommRingCat.of Punctured)⟶Spec (CommRingCat.of R)) q,?_⟩
  exact congrArg (fun f=>f q) punctured_overlap.symm

lemma affine_cover (c:Fin 4→ℚˣ) (p:PrimeSpectrum R) :
    p∈PrimeSpectrum.basicOpen (X:R) ∨
    p∈PrimeSpectrum.basicOpen (ReciprocalInfinityBase318.reciprocalDenominator c):=by
  by_cases hx:X∈p.asIdeal
  · right
    change ReciprocalInfinityBase318.reciprocalDenominator c∉p.asIdeal
    intro hd
    have hsub:ReciprocalInfinityBase318.reciprocalDenominator c-
        C ((ReciprocalInfinityBase318.reciprocalDenominator c).coeff 0)∈p.asIdeal:=
      Ideal.mem_of_dvd p.asIdeal Polynomial.X_dvd_sub_C hx
    have hc:C ((ReciprocalInfinityBase318.reciprocalDenominator c).coeff 0)∈p.asIdeal:=by
      simpa using p.asIdeal.sub_mem hd hsub
    have hcoeff:(ReciprocalInfinityBase318.reciprocalDenominator c).coeff 0≠0:=by
      rw [Polynomial.coeff_zero_eq_eval_zero,ReciprocalInfinityBase318.reciprocalDenominator_at_zero]
      exact Finset.prod_ne_zero_iff.mpr (fun j _=>div_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal hc
      (Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hcoeff)))
  · exact Or.inl hx

/-- The entire t-chart and the genuine reciprocal infinity open cover the
projective contact line. The reciprocal denominator's constant term is a unit. -/
theorem base_cover (c:Fin 4→ℚˣ) :
    (JLineAtlas318.chart ℚ 1).opensRange⊔(InfinityGlobalBase318.baseOpen c).opensRange=⊤:=by
  apply top_unique
  intro x _
  have hx:x∈(⨆j,(ContactGlobalProper318.targetCover j).1):=by
    rw [ContactGlobalProper318.targetCover_covers]
    trivial
  obtain ⟨j,hj⟩:=TopologicalSpace.Opens.mem_iSup.mp hx
  change x∈JLineAtlas318.chart ℚ j ''ᵁ ⊤ at hj
  rw [Scheme.Hom.image_top_eq_opensRange] at hj
  fin_cases j
  · obtain ⟨p,rfl⟩:=hj
    rcases affine_cover c p with hp|hp
    · exact Or.inl (chart0_X_in_chart1 p hp)
    · obtain ⟨q,rfl⟩:=(Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range
        (InfinityGlobalBase318.A c) (ReciprocalInfinityBase318.reciprocalDenominator c)) p).mpr hp
      exact Or.inr ⟨q,rfl⟩
  · exact Or.inl hj
end ContactSmoothBaseCover318
