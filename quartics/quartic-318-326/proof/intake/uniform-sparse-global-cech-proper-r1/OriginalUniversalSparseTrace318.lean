module
public import OriginalUniversalSparseSolutions318
public import OriginalUniformSparseJet318
public section
noncomputable section
namespace OriginalUniversalSparseTrace318
open Polynomial OriginalSparsePolynomialReflection318 OriginalUniversalSparseCoefficients318
open OriginalUniversalSparseSolutions318 OriginalUniformSparseJet318 OriginalUniversalSparsePolynomial318
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
variable {K : Type*} [Field K]
@[expose] def vs : Fin 3 → Tri := ![v0,v1,v2]
@[expose] def vt : Fin 3 → Tri := ![v3,v4,v5]
@[expose] def qs : Fin 3 → Tri := ![q0,q1,q2]
@[expose] def qt : Fin 3 → Tri := ![q3,q4,q5]
theorem rel_s (s t : K) (i : Fin 3) :
    read s t (vs i)*(sextic s t).derivative+read s t (qs i)*sextic s t=
    C (denom s t)*(X^(i:ℕ)*pol (gS s t)) := by
  fin_cases i
  · exact row0 s t
  · exact row1 s t
  · exact row2 s t
theorem rel_t (s t : K) (i : Fin 3) :
    read s t (vt i)*(sextic s t).derivative+read s t (qt i)*sextic s t=
    C (denom s t)*(X^(i:ℕ)*pol (gT s t)) := by
  fin_cases i
  · exact row3 s t
  · exact row4 s t
  · exact row5 s t
@[expose] def jet (s t ds dt : K) := C ds*pol (gS s t)+C dt*pol (gT s t)
@[expose] def rem (s t ds dt : K) (i : Fin 3) :=
  C (denom s t)⁻¹*(C ds*read s t (vs i)+C dt*read s t (vt i))
private theorem normalize {R : Type*} [CommRing R] (u v f g d k f' : R)
    (h : u*f'+v*f=d*g) (hn : k*d=1) :
    g-(k*u)*f'=f*(k*v) := by
  calc
    _ = k*(d*g-u*f') := by rw [mul_sub,← mul_assoc,hn]; ring
    _ = _ := by rw [← h]; ring
/-- Actual canonical six-branch input, including an inverse of F' and all three
true degree-five Bézout remainders, without assuming a Cramer or factorization oracle. -/
@[expose] def data (s t ds dt : K) (hs : s≠0) (hd : denom s t≠0) : OriginalSeparableSexticJet318.Data K where
  F := sextic s t
  G := jet s t ds dt
  degree := sextic_degree _ _ hs
  jet_degree := by
    apply natDegree_add_le_of_degree_le <;> exact (natDegree_C_mul_le ..).trans (pol_bound _ _ (by simp [gS,gT]))
  inverse := C (denom s t)⁻¹*read s t v6
  inverse_quotient := -(C (denom s t)⁻¹*read s t q6)
  inverse_relation := by
    have hi : C ((denom s t)⁻¹)*C (denom s t)=1 := by rw [← map_mul,inv_mul_cancel₀ hd,map_one]
    have h := normalize _ _ _ _ _ _ _ (row6 s t) hi
    linear_combination -h
  remainder := rem s t ds dt
  small := by
    intro i
    apply (natDegree_C_mul_le ..).trans
    apply natDegree_add_le_of_degree_le
    · apply (natDegree_C_mul_le ..).trans
      apply pol_bound
      rw [List.length_map]; fin_cases i <;> decide +kernel
    · apply (natDegree_C_mul_le ..).trans
      apply pol_bound
      rw [List.length_map]; fin_cases i <;> decide +kernel
  relation := by
    intro i
    have hi : C ((denom s t)⁻¹)*C (denom s t)=1 := by rw [← map_mul,inv_mul_cancel₀ hd,map_one]
    refine ⟨C (denom s t)⁻¹*(C ds*read s t (qs i)+C dt*read s t (qt i)),?_⟩
    apply normalize _ _ _ _ _ _ _ _ hi
    unfold jet
    linear_combination (C ds)*rel_s s t i + (C dt)*rel_t s t i

@[expose] def diagS (s t : K) : Fin 3 → K := ![H00 s t,0,H02 s t]
@[expose] def diagT (s t : K) : Fin 3 → K := ![H10 s t,0,H12 s t]
theorem topS (s t : K) (i : Fin 3) :
    (read s t (vs i)).coeff 5=jachead s t*diagS s t i := by
  fin_cases i <;> simp [vs,OriginalUniversalSparseCoefficients318.read,pol_coeff,v0,v1,v2,co,value,jachead,diagS,H00,H02] <;> ring
theorem topT (s t : K) (i : Fin 3) :
    (read s t (vt i)).coeff 5=jachead s t*diagT s t i := by
  fin_cases i <;> simp [vt,OriginalUniversalSparseCoefficients318.read,pol_coeff,v3,v4,v5,co,value,jachead,diagT,H10,H12] <;> ring
@[expose] def factor (s t : K) : K := -2*jachead s t / (denom s t*s^2)
theorem entry (s t ds dt : K) (hs : s≠0) (hd : denom s t≠0) (i : Fin 3) :
    -2*((rem s t ds dt i).coeff 5/(sextic s t).leadingCoeff)=
      factor s t * (diagS s t i*ds+diagT s t i*dt) := by
  simp only [rem,coeff_C_mul,coeff_add,topS,topT,sextic_leading s t hs,factor]
  field_simp
open OriginalSexticJetMarked318 OriginalSeparableSexticJet318 in
theorem true_branch_sum (s t ds dt : K) (hs : s≠0) (hd : denom s t≠0) (i : Fin 3) :
    algebraMap K (sextic s t).SplittingField (factor s t * (diagS s t i*ds+diagT s t i*dt)) =
      branchMoment (splittingCertificate (data s t ds dt hs hd)) i := by
  rw [← entry s t ds dt hs hd i]
  exact moment_transport (data s t ds dt hs hd) i
end OriginalUniversalSparseTrace318
#print axioms OriginalUniversalSparseTrace318.true_branch_sum
