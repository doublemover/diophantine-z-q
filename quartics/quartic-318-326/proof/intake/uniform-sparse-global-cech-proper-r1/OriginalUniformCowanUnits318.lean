module
public import OriginalScalarCowanRegisters318
public section
namespace OriginalUniformCowanUnits318
open OriginalUniformCowanData318 OriginalUniformFractionCert318 OriginalMarkedIntPolynomialCertificate318 OriginalRadixHZCertificate318 OriginalScalarNamedUnits318
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]
theorem certified_unit (z : K) (xs : List PairE) (ds : List ℕ) (ts : List Term) (c : ℤ)
    (fs : List (ℕ×ℕ)) (hd : ∀ v∈xs, Ev z v.2≠0) (hc : c≠0)
    (hf : ∀ i, horner z (factor i)≠0) (ht : valid ds ts=true)
    (he : Ev z (.add (expr xs ts) (.scale (-c) (prodFactors fs)))=0) :
    value (ratios z xs) ts≠0 := by
  have hh := expr_sound z xs ds ts hd ht
  change Ev z (expr xs ts) + ((-c :ℤ):K)*Ev z (prodFactors fs)=0 at he
  rw [hh] at he
  intro hz
  rw [hz,zero_mul,zero_add] at he
  exact (mul_ne_zero (by exact_mod_cast neg_ne_zero.mpr hc) (prod_ne _ hf fs)) he
@[expose] def varsN : List PairE := [regn]
@[expose] def termsN : List Term := [(1,[(1,0)])]
omit [CharZero K] in
theorem valueN (n : K) : value [n] termsN = n := by
  simp only [value,termsN,mno]
  ring
theorem nzN (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z regn)≠0 := by
  have hv := certified_unit z varsN [1] termsN (3) [(14,1)] (by
    intro v hv
    simp only [varsN,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl
    · exact hd .regn) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regn)] termsN≠0 at hv
  rwa [valueN] at hv
@[expose] def varsGap : List PairE := [regn]
@[expose] def termsGap : List Term := [(1,[(1,0)]),(-5,[(0,1)])]
omit [CharZero K] in
theorem valueGap (n : K) : value [n] termsGap = n-5 := by
  simp only [value,termsGap,mno]
  ring
theorem nzGap (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z regn)-5≠0 := by
  have hv := certified_unit z varsGap [1] termsGap (1) [(13,1)] (by
    intro v hv
    simp only [varsGap,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl
    · exact hd .regn) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regn)] termsGap≠0 at hv
  rwa [valueGap] at hv
@[expose] def varsSplit : List PairE := [regm,regn]
@[expose] def termsSplit : List Term := [(1,[(2,0),(0,1)]),(-1,[(0,2),(1,0)])]
omit [CharZero K] in
theorem valueSplit (m n : K) : value [m,n] termsSplit = m^2-n := by
  simp only [value,termsSplit,mno]
  ring
theorem nzSplit (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z regm)^2-(OriginalUniformCowanData318.read z regn)≠0 := by
  have hv := certified_unit z varsSplit [2,1] termsSplit (-3125) [(15,2),(2,6),(3,6),(10,2),(16,2),(17,2),(18,2),(19,2),(20,2),(21,2),(22,2),(4,6),(5,6),(6,6),(23,2),(8,1),(24,2),(25,2),(7,3),(12,2)] (by
    intro v hv
    simp only [varsSplit,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl
    · exact hd .regm
    · exact hd .regn) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regm),(OriginalUniformCowanData318.read z regn)] termsSplit≠0 at hv
  rwa [valueSplit] at hv
@[expose] def varsNorm : List PairE := [regm,regn,rega,regb]
@[expose] def termsNorm : List Term := [(-1,[(2,0),(0,1),(0,2),(2,0)]),(1,[(0,2),(1,0),(0,2),(2,0)]),(1,[(0,2),(0,1),(2,0),(0,2)])]
omit [CharZero K] in
theorem valueNorm (m n a b : K) : value [m,n,a,b] termsNorm = a^2-b^2*(m^2-n) := by
  simp only [value,termsNorm,mno]
  ring
theorem nzNorm (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z rega)^2-(OriginalUniformCowanData318.read z regb)^2*((OriginalUniformCowanData318.read z regm)^2-(OriginalUniformCowanData318.read z regn))≠0 := by
  have hv := certified_unit z varsNorm [2,1,2,2] termsNorm (9293598720000) [(15,2),(2,6),(3,6),(0,2),(10,2),(16,2),(17,2),(18,2),(19,2),(20,2),(21,2),(22,2),(4,6),(5,6),(6,6),(23,2),(8,1),(24,2),(7,2),(25,2),(12,4),(13,3),(14,4)] (by
    intro v hv
    simp only [varsNorm,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hd .regm
    · exact hd .regn
    · exact hd .rega
    · exact hd .regb) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regm),(OriginalUniformCowanData318.read z regn),(OriginalUniformCowanData318.read z rega),(OriginalUniformCowanData318.read z regb)] termsNorm≠0 at hv
  rwa [valueNorm] at hv
@[expose] def varsE : List PairE := [regm,regn]
@[expose] def termsE : List Term := [(2,[(1,0),(2,0)]),(-10,[(1,0),(1,1)]),(10,[(0,1),(2,0)]),(-90,[(0,1),(1,1)]),(216,[(0,1),(0,2)])]
omit [CharZero K] in
theorem valueE (m n : K) : value [m,n] termsE = (n^2-5*n)*(2*m)+10*n^2-90*n+216 := by
  simp only [value,termsE,mno]
  ring
theorem nzE (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : ((OriginalUniformCowanData318.read z regn)^2-5*(OriginalUniformCowanData318.read z regn))*(2*(OriginalUniformCowanData318.read z regm))+10*(OriginalUniformCowanData318.read z regn)^2-90*(OriginalUniformCowanData318.read z regn)+216≠0 := by
  have hv := certified_unit z varsE [1,2] termsE (18750) [(2,6),(3,6),(4,6),(5,6),(6,6),(7,3),(13,1),(14,1)] (by
    intro v hv
    simp only [varsE,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl
    · exact hd .regm
    · exact hd .regn) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regm),(OriginalUniformCowanData318.read z regn)] termsE≠0 at hv
  rwa [valueE] at hv
@[expose] def varsJ : List PairE := [regJ]
@[expose] def termsJ : List Term := [(1,[(1,0)])]
omit [CharZero K] in
theorem valueJ (J : K) : value [J] termsJ = J := by
  simp only [value,termsJ,mno]
  ring
theorem nzJ (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z regJ)≠0 := by
  have hv := certified_unit z varsJ [1] termsJ (2) [(11,1)] (by
    intro v hv
    simp only [varsJ,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl
    · exact hd .regJ) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regJ)] termsJ≠0 at hv
  rwa [valueJ] at hv
@[expose] def varsX : List PairE := [regX]
@[expose] def termsX : List Term := [(1,[(1,0)])]
omit [CharZero K] in
theorem valueX (X : K) : value [X] termsX = X := by
  simp only [value,termsX,mno]
  ring
theorem nzX (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z regX)≠0 := by
  have hv := certified_unit z varsX [1] termsX (1) [(7,1)] (by
    intro v hv
    simp only [varsX,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl
    · exact hd .regX) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regX)] termsX≠0 at hv
  rwa [valueX] at hv
@[expose] def varsY : List PairE := [regY]
@[expose] def termsY : List Term := [(1,[(1,0)])]
omit [CharZero K] in
theorem valueY (Y : K) : value [Y] termsY = Y := by
  simp only [value,termsY,mno]
  ring
theorem nzY (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z regY)≠0 := by
  have hv := certified_unit z varsY [1] termsY (1) [(8,1)] (by
    intro v hv
    simp only [varsY,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl
    · exact hd .regY) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regY)] termsY≠0 at hv
  rwa [valueY] at hv
@[expose] def varsBB : List PairE := [regBB]
@[expose] def termsBB : List Term := [(1,[(1,0)])]
omit [CharZero K] in
theorem valueBB (BB : K) : value [BB] termsBB = BB := by
  simp only [value,termsBB,mno]
  ring
theorem nzBB (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z regBB)≠0 := by
  have hv := certified_unit z varsBB [1] termsBB (1) [(12,1)] (by
    intro v hv
    simp only [varsBB,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl
    · exact hd .regBB) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regBB)] termsBB≠0 at hv
  rwa [valueBB] at hv
@[expose] def varsCC : List PairE := [regCC]
@[expose] def termsCC : List Term := [(1,[(1,0)])]
omit [CharZero K] in
theorem valueCC (CC : K) : value [CC] termsCC = CC := by
  simp only [value,termsCC,mno]
  ring
theorem nzCC (z : K) (hd : ∀ i, Ev z (OriginalScalarCowanRegisters318.reg i).2≠0) (hf : ∀ i, horner z (factor i)≠0) : (OriginalUniformCowanData318.read z regCC)≠0 := by
  have hv := certified_unit z varsCC [1] termsCC (-7) [(2,2),(3,2),(4,2),(5,2),(6,2),(7,1)] (by
    intro v hv
    simp only [varsCC,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl
    · exact hd .regCC) (by decide +kernel) hf (by decide +kernel) (certificate z (2^4096) _ (by decide +kernel) (by decide +kernel))
  change value [(OriginalUniformCowanData318.read z regCC)] termsCC≠0 at hv
  rwa [valueCC] at hv
end OriginalUniformCowanUnits318
#print axioms OriginalUniformCowanUnits318.nzNorm
