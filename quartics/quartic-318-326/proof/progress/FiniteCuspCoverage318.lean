module
public import RotatedStabilizer318
public import GammaOneAtlas318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open scoped MatrixGroups Modular
namespace FiniteCuspCoverage318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def rotations (N:ℕ) : Set SL(2,ℤ) :=
  Set.range (fun q:SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma1 N=>q.out⁻¹)

theorem rotations_finite (N:ℕ) [NeZero N] : (rotations N).Finite := by
  letI:Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma1 N):=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact Set.finite_range _

/-- Actual left Gamma1 coset representatives, obtained from the right-oriented
Mathlib quotient by inversion. Gamma1 is not assumed normal. -/
theorem rotations_cover (N:ℕ) (g:SL(2,ℤ)) :
    ∃r∈rotations N,∃gamma:CongruenceSubgroup.Gamma1 N,g=gamma.val*r := by
  let q:SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma1 N := ⟦g⁻¹⟧
  have hq:(⟦q.out⟧:SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma1 N)=⟦g⁻¹⟧:=q.out_eq
  have hm:q.out⁻¹*g⁻¹∈CongruenceSubgroup.Gamma1 N :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
  have hi:g*q.out∈CongruenceSubgroup.Gamma1 N := by
    simpa only [mul_inv_rev,inv_inv] using (CongruenceSubgroup.Gamma1 N).inv_mem hm
  refine ⟨q.out⁻¹,⟨q,rfl⟩,⟨g*q.out,hi⟩,?_⟩
  simp

theorem quotient_smul (N:ℕ) (gamma:CongruenceSubgroup.Gamma1 N) (tau:UpperHalfPlane) :
    quotientMap N (gamma.val•tau)=quotientMap N tau := by
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact ⟨⟨positiveMatrix N gamma,⟨gamma,rfl⟩⟩,rfl⟩

/-- Every actual quotient point has a representative in one of finitely many
rotated full modular fundamental domains. -/
theorem fundamental_cover (N:ℕ) (b:Base (image N)) :
    ∃r∈rotations N,∃tau∈ModularGroup.fd,quotientMap N (r•tau)=b := by
  obtain ⟨z,rfl⟩:=quotient_surjective N b
  obtain ⟨g,hg⟩:=ModularGroup.exists_smul_mem_fd z
  obtain ⟨r,hr,gamma,he⟩:=rotations_cover N g⁻¹
  refine ⟨r,hr,g•z,hg,?_⟩
  have hz:gamma.val•(r•(g•z))=z := by
    rw [←mul_smul,←he,inv_smul_smul]
  exact (quotient_smul N gamma (r•(g•z))).symm.trans (congrArg (quotientMap N) hz)

@[expose] def compactCore (N:ℕ) (A:ℝ) : Set (Base (image N)) :=
  ⋃r∈rotations N,(fun tau:UpperHalfPlane=>quotientMap N (r•tau)) ''
    ModularGroup.truncatedFundamentalDomain A

@[expose] def cuspRegion (N:ℕ) (g:SL(2,ℤ)) (A:ℝ) : Set (Base (image N)) :=
  (fun tau:UpperHalfPlane=>quotientMap N (g•tau)) '' {tau | A<tau.im}

theorem compactCore_isCompact (N:ℕ) [NeZero N] (A:ℝ) : IsCompact (compactCore N A) := by
  apply (rotations_finite N).isCompact_biUnion
  intro g hg
  apply (ModularGroup.isCompact_truncatedFundamentalDomain A).image
  apply (continuous_quotient_mk').comp
  have he:(fun tau:UpperHalfPlane=>g•tau)=(fun tau:UpperHalfPlane=>(g:GL (Fin 2) ℝ)•tau):=
    funext (ModularGroup.sl_moeb g)
  exact (continuous_const_smul (g:GL (Fin 2) ℝ)).congr
    (fun tau => (ModularGroup.sl_moeb g tau).symm)

/-- Actual finite cusp-end coverage: the quotient is a compact core together
with finitely many rotated high regions, for any chosen truncation height. -/
theorem compact_core_and_cusps (N:ℕ) (A:ℝ) (b:Base (image N)) :
    b∈compactCore N A ∨ ∃g∈rotations N,b∈cuspRegion N g A := by
  obtain ⟨g,hg,tau,htau,rfl⟩:=fundamental_cover N b
  by_cases h:tau.im≤A
  · left
    exact Set.mem_iUnion.mpr ⟨g,Set.mem_iUnion.mpr ⟨hg,⟨tau,⟨htau,h⟩,rfl⟩⟩⟩
  · right
    exact ⟨g,hg,⟨tau,lt_of_not_ge h,rfl⟩⟩

end FiniteCuspCoverage318
