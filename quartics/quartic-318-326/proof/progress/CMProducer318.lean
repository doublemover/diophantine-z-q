module
public import CMDiscriminant318
public import CMIsogeny318
public section
noncomputable section
open scoped Real
namespace CMProducer318
set_option maxHeartbeats 0

/-- Actual fundamental discriminant, prime-support, eta-product, averaging,
and dimension-two isogeny inequalities compose to the original-normalized
CM surface bound. Geometric period/height and isogeny inputs remain explicit. -/
theorem original_surface_bound (D:ℤ) (B q:ℕ) (z:Fin q→ℂ)
    (R d deg hE hAprime hA:ℝ) (hD:Int.IsFundamentalDiscr D) (hB:B≠0)
    (hsupport:∀p:ℕ,p.Prime→p∣D.natAbs→p∣B)
    (hRadical:(CMDiscriminant318.radical B:ℝ)≤R) (hR:1≤R) (hq:1≤q)
    (hy:∀i,Real.sqrt 3/2≤(z i).im) (hupper:∀i,(z i).im≤Real.sqrt D.natAbs/2)
    (hSilverman:hE=(∑i,CMArchimedean318.summand (z i))/(q:ℝ))
    (hproduct:hAprime=2*hE) (hd:0<d) (hdegree:d≤576) (hdeg:0<deg)
    (hGR:deg≤(CMIsogeny318.Xi d hAprime)^2)
    (hvariation:hA≤hAprime+(1/2)*Real.log deg) : hA<854*R := by
  apply CMIsogeny318.cm_surface_from_periods q hq z D.natAbs R d deg hE hAprime hA
    (by positivity) hR
    (CMDiscriminant318.real_discriminant_bound D B R hD hB hsupport hRadical)
    hy hupper hSilverman hproduct hd hdegree hdeg hGR hvariation

end CMProducer318
#print axioms CMProducer318.original_surface_bound
