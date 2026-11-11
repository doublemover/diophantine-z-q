module
public import PELNormalizerOctagonWholeImages318
public section
noncomputable section
namespace PELNormalizerOctagonOrbitSigns318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELLevelThreeSimilitudes318 QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELNormalizerOctagonMinimum318 PELNormalizerOctagonDomain318
open PELNormalizerOctagonAffine318 PELNormalizerOctagonStrata318
open PELNormalizerOctagonWholeImages318 PELNormalizerOctagonRealImages318
open PELPositiveNormalizerKlein318 NormalizerVertexEnergyMinimum318
set_option maxHeartbeats 5000000

/-- Actual primitive coordinates and their literal point equality are
constructed together. No arbitrary norm vector is declared a normalizer. -/
theorem primitive_point_equality (g : positiveNormalizer) (τ : HalfPlane)
    (he : height (baseAction g τ)=height τ) :
    ∃ (q : ℚ) (i : Fin 16) (x : Coordinates),q≠0 ∧
      integerNorm x=(allowedNorm i:ℤ) ∧ (g.val:B)=q • embed x ∧
      realDen (embed x) (scaledFirst τ) (scaledSecond τ)=(allowedNorm i:ℝ) := by
  let G : PELActualOrderNormalizer318.normalizer := ⟨g.val,g.property.1⟩
  obtain ⟨q,x,z,w,hg,hx,hprim,hdiv,hnorm⟩ :=
    PELNormalizerPrimitiveRepresentative318.primitive_representative G
  have hq : 0<(q:ℚ)^2 := sq_pos_of_ne_zero q.ne_zero
  have hNQ : 0<(integralNorm x:ℚ) := by
    have hh : 0<(q:ℚ)^2*(integralNorm x:ℚ) := by rw [←hnorm]; exact g.property.2
    exact pos_of_mul_pos_left hh hq.le
  have hN : 0<integralNorm x := by exact_mod_cast hNQ
  let N := (integralNorm x).toNat
  have hNZ : (N:ℤ)=integralNorm x := Int.toNat_of_nonneg hN.le
  have hNp : 0<N := by exact_mod_cast (show (0:ℤ)<(N:ℤ) by rwa [hNZ])
  have hNd : N∣210 := by exact_mod_cast (show (N:ℤ)∣210 by rwa [hNZ])
  obtain ⟨i,hi⟩ := positive_divisor_cases N hNp hNd
  have hxi : integerNorm x=(allowedNorm i:ℤ) := by
    change integralNorm x=(allowedNorm i:ℤ)
    rw [←hNZ,hi]
  have hval : (g.val:B)=(q:ℚ) • embed x := by
    change (G.val:B)=_
    rw [hg]
    change algebraMap ℚ B (q:ℚ)*(w.val:B)=_
    rw [←hx,Algebra.smul_def]
  have hnormR : (reducedNorm (g.val:B):ℝ)=(q:ℝ)^2*(allowedNorm i:ℝ) := by
    have hh := hnorm
    change reducedNorm (g.val:B)=(q:ℚ)^2*(integralNorm x:ℚ) at hh
    have hnx : integralNorm x=(allowedNorm i:ℤ) := hxi
    rw [hnx] at hh
    exact_mod_cast hh
  have hm := positive_height_multiplier g τ
  rw [he] at hm
  have hnR : 0<(reducedNorm (g.val:B):ℝ) := by exact_mod_cast g.property.2
  have hr : realDen (g.val:B) (scaledFirst τ) (scaledSecond τ)/
      (reducedNorm (g.val:B):ℝ)=1 := by nlinarith [height_pos τ]
  have hd : realDen (g.val:B) (scaledFirst τ) (scaledSecond τ)=
      (reducedNorm (g.val:B):ℝ) := by
    simpa only [one_mul] using (div_eq_iff hnR.ne').mp hr
  rw [hnormR,hval,realDen_smul] at hd
  have hqR : 0<(q:ℝ)^2 := by exact_mod_cast hq
  refine ⟨q,i,x,q.ne_zero,hxi,hval,?_⟩
  nlinarith

/-- No hidden identifications anywhere in the actual original octagon:
every entire-normalizer orbit relation is a coordinate sign change, and
strict interior points permit only the common sign (identity/center210). -/
theorem original_octagon_signs (g : positiveNormalizer) (τ : HalfPlane)
    (hτ : inequalities (scaledFirst τ) (scaledSecond τ))
    (hg : inequalities (scaledFirst (baseAction g τ)) (scaledSecond (baseAction g τ))) :
    ∃ a b : Bool,
      (scaledFirst (baseAction g τ),scaledSecond (baseAction g τ))=
        (signR a (scaledFirst τ),signR b (scaledSecond τ)) ∧
      (strict (scaledFirst τ,scaledSecond τ) → a=b) := by
  obtain ⟨q,i,x,hq,hn,hval,he⟩ := primitive_point_equality g τ (octagon_orbit_height τ g hτ hg)
  obtain ⟨a,b,hA,hY,hs⟩ := whole_integer_rows i x hn
    (scaledFirst τ,scaledSecond τ) hτ he
  have hden : realRow (embed x) 2 (scaledFirst τ) (scaledSecond τ)=(allowedNorm i:ℝ) := he
  refine ⟨a,b,?_,hs⟩
  apply original_coordinates_of_rows g q hq x hval τ
  · rw [hden,hA,mul_comm]
  · rw [hden,hY,mul_comm]
end PELNormalizerOctagonOrbitSigns318
