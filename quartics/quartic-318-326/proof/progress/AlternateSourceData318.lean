module
public import AlternateRatioKernel318
public import AlternateFormal318
public section
namespace AlternateSourceData318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay CompressedOrientation318
open RawAlternatePade318 Pade21Domains
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

@[expose] def polynomial (w:Assignment) : Fin 4→K :=
  ![polynomial1 w,polynomial2 w,polynomial3 w,polynomial4 w]
@[expose] def rawRatio (w:Assignment) : Fin 4→K :=
  ![rawRatio1 w,rawRatio2 w,rawRatio3 w,rawRatio4 w]
@[expose] def full (j:Fin 4) : Bool := decide (j≠0)

theorem source_ratios (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) (j:Fin 4) :
    commonLog w*rawRatio w j= -RawRootDifference318.u w j*polynomial w j := by
  fin_cases j <;> simp only [rawRatio,polynomial,RawRootDifference318.u,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact source_ratio1 S w source
  · exact source_ratio2 S w source
  · exact source_ratio3 S w source
  · exact source_ratio4 S w source

theorem source_ratio_eq (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hs:shift w≠0) (j:Fin 4) :
    rawRatio w j=(-RawRootDifference318.u w j*polynomial w j)/commonLog w := by
  apply (eq_div_iff (fun h=>hs ((source_commonLog_zero S w source).mp h))).mpr
  simpa only [mul_comm] using source_ratios S w source j

theorem source_identity (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hs:shift w=0) : ∀j,RawRootDifference318.u w j=0 := by
  intro j
  fin_cases j <;> simp only [RawRootDifference318.u,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact source_identity_branch1 S w source hs
  · exact source_identity_branch2 S w source hs
  · exact source_identity_branch3 S w source hs
  · exact source_identity_branch4 S w source hs

variable (p:ℕ) [Fact p.Prime]

theorem mapped_polynomial (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4) :
    φ (polynomial w j)=AlternateRatioKernel318.approximation p (full j)
      (φ (RawRootDifference318.v w j)-1) := by
  fin_cases j <;> simp only [polynomial,RawRootDifference318.v,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · simp [full,AlternateRatioKernel318.approximation,polynomial1,delta1,map_div₀]
    erw [map_ofNat φ 5]
  · rw [source_polynomial2_eq S w source]
    simp [full,AlternateRatioKernel318.approximation,delta2,PJ,QJ,map_div₀]
    erw [map_ofNat φ 12,map_ofNat φ 65,map_ofNat φ 2,map_ofNat φ 195,map_ofNat φ 5,map_ofNat φ 13]
  · rw [source_polynomial3_eq S w source]
    simp [full,AlternateRatioKernel318.approximation,delta3,PJ,QJ,map_div₀]
    erw [map_ofNat φ 12,map_ofNat φ 65,map_ofNat φ 2,map_ofNat φ 195,map_ofNat φ 5,map_ofNat φ 13]
  · rw [source_polynomial4_eq S w source]
    simp [full,AlternateRatioKernel318.approximation,delta4,PJ,QJ,map_div₀]
    erw [map_ofNat φ 12,map_ofNat φ 65,map_ofNat φ 2,map_ofNat φ 195,map_ofNat φ 5,map_ofNat φ 13]

theorem mapped_commonLog (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) :
    φ (commonLog w)=φ (CompressedGlobal318.zV w)*
      (PG (φ (D*(fV w)^2))/QG (φ (D*(fV w)^2))) := by
  rw [source_commonLog_eq S w source,source_polynomial0_eq S w source]
  simp only [map_mul,map_div₀,PG,QG,map_add,map_sub,map_pow,map_ofNat,map_mul,map_div₀,map_one]

theorem mapped_ratio (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hs:shift w≠0) (j:Fin 4) :
    φ (rawRatio w j)=
      (-φ (RawRootDifference318.u w j)*AlternateRatioKernel318.approximation p (full j)
        (φ (RawRootDifference318.v w j)-1))/
      (φ (CompressedGlobal318.zV w)*(PG (φ (D*(fV w)^2))/QG (φ (D*(fV w)^2)))) := by
  rw [source_ratio_eq S w source hs j,map_div₀,map_mul,map_neg,
    mapped_polynomial p φ S w source j,mapped_commonLog p φ S w source]

end AlternateSourceData318
#print axioms AlternateSourceData318.mapped_ratio
