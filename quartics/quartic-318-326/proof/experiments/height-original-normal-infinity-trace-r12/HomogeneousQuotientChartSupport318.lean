module
public import HomogeneousQuotientChart318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public section
noncomputable section
namespace HomogeneousQuotientChartSupport318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
open HomogeneousQuotientChart318 HomogeneousLocalization
variable {ι:Type*}
local instance standardGrading:GradedAlgebra (grading (ι:=ι)):=MvPolynomial.gradedAlgebra
variable (j:ι)
@[expose] def chartMorphism:Spec (CommRingCat.of (Chart j))⟶AlgebraicGeometry.Proj grading:=
  Proj.awayι grading (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j) (by norm_num)
lemma chart_nonvanishing(q:PrimeSpectrum (Chart j)):
    MvPolynomial.X j∉(chartMorphism j q).asHomogeneousIdeal:=by
  have h:chartMorphism j q∈(chartMorphism j).opensRange:=⟨q,rfl⟩
  rw [chartMorphism,Proj.opensRange_awayι] at h
  exact h
lemma fraction_multiply_coordinate(n:ℕ)(p:Equations (ι:=ι))(hp:p.IsHomogeneous n):
    fraction j (n+1) (p*MvPolynomial.X j) (hp.mul (MvPolynomial.isHomogeneous_X ℂ j))=
      fraction j n p hp:=by
  apply HomogeneousLocalization.val_injective
  simp only [fraction,HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [OneMemClass.coe_one,one_mul]
  rw [pow_succ]
  ring

lemma positive_fraction_mem(q:PrimeSpectrum (Chart j))(n:ℕ)(hn:0<n)
    (p:Equations (ι:=ι))(hp:p.IsHomogeneous n):
    fraction j n p hp∈q.asIdeal↔p∈(chartMorphism j q).asHomogeneousIdeal:=by
  have he:=Proj.awayι_preimage_basicOpen (𝒜:=grading)
    (f:=MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j) (by norm_num)
    (g:=p) hp hn
  have hmem:=congrArg (fun U=>(q∈U)) he
  change (p∉(chartMorphism j q).asHomogeneousIdeal)=
    (HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X ℂ j) hp
      ∉q.asIdeal) at hmem
  have hf:HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X ℂ j) hp=fraction j n p hp:=by
    simp only [HomogeneousLocalization.Away.isLocalizationElem,pow_one,fraction]
  rw [hf] at hmem
  exact (not_iff_not.mp (iff_of_eq hmem)).symm

/-- Membership in the actual affine-chart prime agrees with numerator
membership in the actual projective point, including degree zero. -/
lemma fraction_mem(q:PrimeSpectrum (Chart j))(n:ℕ)(p:Equations (ι:=ι))
    (hp:p.IsHomogeneous n):
    fraction j n p hp∈q.asIdeal↔p∈(chartMorphism j q).asHomogeneousIdeal:=by
  have h:=positive_fraction_mem j q (n+1) (Nat.zero_lt_succ n)
    (p*MvPolynomial.X j) (hp.mul (MvPolynomial.isHomogeneous_X ℂ j))
  rw [fraction_multiply_coordinate] at h
  rw [(chartMorphism j q).isPrime.mul_mem_iff_mem_or_mem] at h
  simpa only [chart_nonvanishing,or_false] using h

/-- Exact full prime-spectrum support of the quotient-chart kernel.
All homogeneous components of every relation are consumed; zero-divisor
powers of the chart coordinate are retained until the genuine prime
nonvanishing condition permits their cancellation. -/
theorem kernel_support(I:Ideal (Equations (ι:=ι)))(hI:I.IsHomogeneous grading)
    (q:PrimeSpectrum (Chart j)):
    RingHom.ker (quotientMap I j)≤q.asIdeal↔
      (I:Set (Equations (ι:=ι)))⊆(chartMorphism j q).asHomogeneousIdeal:=by
  constructor
  · intro h p hp
    rw [←MvPolynomial.sum_homogeneousComponent p]
    apply (chartMorphism j q).asHomogeneousIdeal.toIdeal.sum_mem
    intro n hn
    apply (fraction_mem j q n _ (MvPolynomial.homogeneousComponent_mem n p)).mp
    apply h
    apply (fraction_zero_iff I j n _ (MvPolynomial.homogeneousComponent_mem n p)).mpr
    refine ⟨0,?_⟩
    simpa only [pow_zero,one_mul] using (MvPolynomial.mem_iff_homogeneousComponent_mem hI p).mp hp n
  · intro h a ha
    obtain ⟨n,p,hp,hpa⟩:=HomogeneousLocalization.Away.mk_surjective grading
      (MvPolynomial.isHomogeneous_X ℂ j) a
    have hp':p.IsHomogeneous n:=by simpa only [smul_eq_mul,mul_one] using hp
    have hpa':fraction j n p hp'=a:=hpa
    rw [←hpa'] at ha ⊢
    obtain ⟨k,hk⟩:=(fraction_zero_iff I j n p hp').mp ha
    apply (fraction_mem j q n p hp').mpr
    rcases (chartMorphism j q).isPrime.mem_or_mem (h hk) with hx|hp
    · exact False.elim ((chart_nonvanishing j q)
        ((chartMorphism j q).isPrime.mem_of_pow_mem k hx))
    · exact hp
end HomogeneousQuotientChartSupport318
