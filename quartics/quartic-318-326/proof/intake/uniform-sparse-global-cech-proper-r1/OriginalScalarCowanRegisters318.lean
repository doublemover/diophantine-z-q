module
public import OriginalUniformCowanData318
public import OriginalScalarNamedUnits318
public section
namespace OriginalScalarCowanRegisters318
open OriginalMarkedIntPolynomialCertificate318 OriginalRadixHZCertificate318
open OriginalScalarEffectiveChart318 OriginalScalarNamedUnits318 OriginalUniformFractionCert318 OriginalUniformCowanData318
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
inductive RegisterCode where
  | regm
  | regn
  | regp
  | regq
  | regh
  | rega
  | regb
  | regT
  | regAA
  | regBB
  | regCC
  | regJ
  | regX
  | regY
deriving DecidableEq, Repr
@[expose] def reg : RegisterCode → PairE
  | .regm => regm
  | .regn => regn
  | .regp => regp
  | .regq => regq
  | .regh => regh
  | .rega => rega
  | .regb => regb
  | .regT => regT
  | .regAA => regAA
  | .regBB => regBB
  | .regCC => regCC
  | .regJ => regJ
  | .regX => regX
  | .regY => regY
@[expose] def content : RegisterCode → ℤ
  | .regm => 24
  | .regn => 1
  | .regp => 24
  | .regq => 1
  | .regh => 56448
  | .rega => 1568
  | .regb => 4900
  | .regT => 1
  | .regAA => 1
  | .regBB => 1
  | .regCC => 1
  | .regJ => 1
  | .regX => 1
  | .regY => 1
@[expose] def divs : RegisterCode → List (ℕ×ℕ)
  | .regm => [(12,1),(13,1),(14,1)]
  | .regn => [(12,2)]
  | .regp => [(12,2),(13,2),(14,2)]
  | .regq => [(12,3)]
  | .regh => [(12,1),(13,1),(14,1)]
  | .rega => [(0,1),(12,1),(14,1)]
  | .regb => [(15,1),(2,3),(3,3),(0,1),(10,1),(16,1),(17,1),(18,1),(19,1),(20,1),(21,1),(22,1),(4,3),(5,3),(6,3),(23,1),(24,1),(7,1),(25,1)]
  | .regT => [(8,1)]
  | .regAA => []
  | .regBB => []
  | .regCC => []
  | .regJ => [(2,2),(3,2),(4,2),(5,2),(6,2),(7,1)]
  | .regX => []
  | .regY => []
@[expose] def delta (i : RegisterCode) : E :=
  .add (reg i).2 (.scale (-(content i)) (prodFactors (divs i)))
theorem denominator {K : Type*} [CommRing K] (z : K) (i : RegisterCode) :
    Ev z (reg i).2 = (content i:K)*Ev z (prodFactors (divs i)) := by
  have he : Ev z (delta i)=0 := by
    cases i <;> exact certificate z (2^2048) _ (by decide +kernel) (by decide +kernel)
  change Ev z (reg i).2+((-content i :ℤ):K)*Ev z (prodFactors (divs i))=0 at he
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg] using he
theorem at_original {K : Type*} [Field K] [CharZero K] (r₀ r₁ r₃ : K) (x : ℚ) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₃ : r₃^2= -21*(119136*(x:K)^2+343)) (i : RegisterCode) :
    Ev ((8*r₃/r₀-15)/(49*r₁/r₀-30)) (reg i).2≠0 := by
  obtain ⟨_,h0,h8,_,hs⟩ := OriginalScalarEffectiveChart318.from_original r₀ r₁ r₃ x hx h₀ h₁ h₃
  rw [denominator]
  have hci : content i≠0 := by cases i <;> decide +kernel
  exact mul_ne_zero (by exact_mod_cast hci) (prod_ne _ (every_factor _ h0 h8 hs) _)
@[expose] def registers : List PairE := [regm,regn,regp,regq,regh,rega,regb,regT,regAA,regBB,regCC,regJ,regX,regY]
/-- Every literal denominator of all fourteen shared Cowan/KS/QM registers is
a unit at every original rational scalar x≠0, without a hidden generic-point premise. -/
theorem from_original {K : Type*} [Field K] [CharZero K] (r₀ r₁ r₃ : K) (x : ℚ) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₃ : r₃^2= -21*(119136*(x:K)^2+343)) :
    ∀ v∈registers, Ev ((8*r₃/r₀-15)/(49*r₁/r₀-30)) v.2≠0 := by
  intro v hv
  simp only [registers,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regm
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regn
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regp
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regq
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regh
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .rega
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regb
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regT
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regAA
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regBB
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regCC
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regJ
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regX
  · exact at_original r₀ r₁ r₃ x hx h₀ h₁ h₃ .regY
end OriginalScalarCowanRegisters318
#print axioms OriginalScalarCowanRegisters318.from_original
