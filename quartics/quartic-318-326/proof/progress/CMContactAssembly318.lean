module
public import CMProducer318
public import CMSurfaceTransfer318
public section
noncomputable section
namespace CMContactAssembly318

/-- Actual CM arithmetic producer composed with the original-normalized geometric comparison.
No surface854R or contact854R premise is supplied. -/
theorem original_contact_bound (D:ℤ) (B q:ℕ) (z:Fin q→ℂ)
    (R d deg hE hAprime hA hContact:ℝ) (hD:Int.IsFundamentalDiscr D) (hB:B≠0)
    (hsupport:∀p:ℕ,p.Prime→p∣D.natAbs→p∣B)
    (hRadical:(CMDiscriminant318.radical B:ℝ)≤R) (hR:1≤R) (hq:1≤q)
    (hy:∀i,Real.sqrt 3/2≤(z i).im) (hupper:∀i,(z i).im≤Real.sqrt D.natAbs/2)
    (hSilverman:hE=(∑i,CMArchimedean318.summand (z i))/(q:ℝ))
    (hproduct:hAprime=2*hE) (hd:0<d) (hdegree:d≤576) (hdeg:0<deg)
    (hGR:deg≤(CMIsogeny318.Xi d hAprime)^2)
    (hvariation:hA≤hAprime+(1/2)*Real.log deg)
    (hGeometric:hContact≤2*hA+120) :
    hContact<2^68*ActualLogWeight318.C^2*R^((49:ℝ)/8)+128 := by
  apply CMSurfaceTransfer318.actual_CM_contact_bound R hA hContact hR
    (CMProducer318.original_surface_bound D B q z R d deg hE hAprime hA hD hB hsupport hRadical hR hq
    hy hupper hSilverman hproduct hd hdegree hdeg hGR hvariation) hGeometric

/-- The exact Yuan/GR dimension-two shift is retained before the geometric comparison. -/
theorem shifted_contact_bound (D:ℤ) (B q:ℕ) (z:Fin q→ℂ)
    (R d deg hE hAprime hA hContact:ℝ) (hD:Int.IsFundamentalDiscr D) (hB:B≠0)
    (hsupport:∀p:ℕ,p.Prime→p∣D.natAbs→p∣B)
    (hRadical:(CMDiscriminant318.radical B:ℝ)≤R) (hR:1≤R) (hq:1≤q)
    (hy:∀i,Real.sqrt 3/2≤(z i).im) (hupper:∀i,(z i).im≤Real.sqrt D.natAbs/2)
    (hSilverman:hE=(∑i,CMArchimedean318.summand (z i))/(q:ℝ))
    (hproduct:hAprime=2*hE) (hd:0<d) (hdegree:d≤576) (hdeg:0<deg)
    (hGR:deg≤(CMIsogeny318.Xi d hAprime)^2)
    (hvariation:hA≤hAprime+(1/2)*Real.log deg)
    (hShifted:ℝ) (hShift:hShifted=hA+Real.log Real.pi)
    (hGeometric:hContact≤2*hShifted+120) :
    hContact<2^68*ActualLogWeight318.C^2*R^((49:ℝ)/8)+128 := by
  exact CMSurfaceTransfer318.actual_CM_shifted_contact_bound R hA hShifted hContact hR
    (CMProducer318.original_surface_bound D B q z R d deg hE hAprime hA hD hB hsupport hRadical hR hq
    hy hupper hSilverman hproduct hd hdegree hdeg hGR hvariation) hShift hGeometric

end CMContactAssembly318
