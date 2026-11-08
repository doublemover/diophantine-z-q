module
public import FifthFixingSigns318
public section
noncomputable section
namespace FifthDifferentialAveraging318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open scoped BigOperators
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- Sum of the actual canonical differential pullbacks of precisely the
eight root-sign automorphisms fixing the whole fifth completed map. -/
@[expose] def signSum:Γ(M,⊤)→+Γ(M,⊤):=
  ∑b∈FifthFixingSigns318.signs,ContactDifferentialCharacters318.action b
lemma signSum_apply (s:Γ(M,⊤)):signSum s=
    ∑b∈FifthFixingSigns318.signs,ContactDifferentialCharacters318.action b s:=by
  simp only [signSum,AddMonoidHom.finsetSum_apply]
/-- Vanishing of the actual eight-sign differential sum on each of the
four complementary elliptic invariant pullbacks. -/
theorem complementary (i:Fin 4):signSum (ContactCharacterDifferentials318.differential i)=0:=by
  rw [signSum_apply]
  simp only [ContactDifferentialCharacters318.eigenrelation]
  rw [←Finset.sum_smul,←map_sum,FifthFixingSigns318.complementary_sum,map_zero,zero_smul]
/-- The actual fifth invariant pullback is fixed by all eight signs, with
unnormalized averaging exactly equal to multiplication by eight. -/
theorem fifth:signSum FifthActualDifferential318.differential=
    ContactCharacterGlobalIndependence318.constants 8 • FifthActualDifferential318.differential:=by
  rw [signSum_apply]
  simp only [FifthGlobalCharacters318.actual_eigenrelation]
  rw [←Finset.sum_smul,←map_sum,FifthFixingSigns318.full_sum]
/-- Normalized averaging is an operation on genuine global intrinsic
sections. This definition alone does not construct a trace to target Omega. -/
@[expose] def average (s:Γ(M,⊤)):Γ(M,⊤):=
  ContactCharacterGlobalIndependence318.constants (1/8) • signSum s
lemma average_add (s t:Γ(M,⊤)):average (s+t)=average s+average t:=by
  simp only [average,map_add,smul_add]
theorem average_complementary (i:Fin 4):average (ContactCharacterDifferentials318.differential i)=0:=by
  rw [average,complementary,smul_zero]
theorem average_fifth:average FifthActualDifferential318.differential=
    FifthActualDifferential318.differential:=by
  rw [average,fifth,smul_smul,←map_mul]
  norm_num
end FifthDifferentialAveraging318
