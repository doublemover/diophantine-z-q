module
public import OriginalBranchResidueLocal318
public import OriginalUniformSparseAffineModel318
public import OriginalUniformSparseReciprocalChart318
public section
noncomputable section
namespace OriginalSparseActualBranch318
open OriginalBranchPlaneLocal318 OriginalBranchResidueLocal318 OriginalUniversalSparsePolynomial318
open OriginalUniformSparseSmoothChart318
variable {k : Type*} [Field k]
abbrev ideal (s t : k) := Ideal.span (Set.range (OriginalUniformSparseAffineModel318.equations s t))
local notation "x₀" => OriginalUniformSparseAffineModel318.x
local notation "y₀" => OriginalUniformSparseAffineModel318.y
local notation "base₀" => OriginalUniformSparseAffineModel318.base
@[expose] def ev (s t α : k) (h : eqVal s t α=0) :
    OriginalUniformSparseAffineModel318.Ring s t →ₐ[k] k := by
  let f := MvPolynomial.aeval (R:=k) (![α,0] : Fin 2→k)
  apply Ideal.Quotient.liftₐ (ideal s t) f
  have hker : ideal s t ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro P ⟨i,rfl⟩
    change f (OriginalUniformSparseAffineModel318.eq s t)=0
    simp [f,OriginalUniformSparseAffineModel318.eq,eqVal] at h ⊢
    linear_combination -h
  exact fun v hv => hker hv
theorem ev_x (s t α : k) (h : eqVal s t α=0) : ev s t α h (x₀ s t)=α := by
  change MvPolynomial.aeval (R:=k) (![α,0] : Fin 2→k) (MvPolynomial.X 0)=α
  simp
theorem ev_y (s t α : k) (h : eqVal s t α=0) : ev s t α h (y₀ s t)=0 := by
  change MvPolynomial.aeval (R:=k) (![α,0] : Fin 2→k) (MvPolynomial.X 1)=0
  simp
theorem polynomial_eq (s t z : k) : (sextic s t).eval z=eqVal s t z := by
  simp [sextic,cvec,pol,eqVal]; ring
theorem genuine (s t : k) : (y₀ s t)^2=Polynomial.aeval (x₀ s t) (sextic s t) := by
  rw [OriginalUniformSparseAffineModel318.relation]
  simp [sextic,cvec,pol,eqVal,OriginalUniformSparseAffineModel318.base,map_ofNat]
  ring
theorem derivative_eq (s t α : k) : (sextic s t).derivative.eval α=derVal s t α := by
  simp only [sextic,cvec,pol,Polynomial.derivative_add,Polynomial.derivative_C,Polynomial.derivative_X,
    Polynomial.derivative_mul,Polynomial.derivative_zero]
  simp [derVal]; ring
theorem branch_uniformizer (s t α : k) (h : eqVal s t α=0) (hs : derVal s t α≠0) :
    let φ:=ev s t α h
    IsLocalRing.maximalIdeal (stalk (I:=ideal s t) φ)=Ideal.span ({toLocal φ (y₀ s t)}:Set (stalk φ)) := by
  exact uniformizer (ideal s t) (ev s t α h) α (sextic s t) (ev_x s t α h) (ev_y s t α h)
    (genuine s t) ((polynomial_eq ..).trans h) (fun hh=>hs ((derivative_eq ..).symm.trans hh))
theorem unit_jac (s t α : k) (h : eqVal s t α=0) (hs : derVal s t α≠0) :
    ev s t α h (Polynomial.aeval (x₀ s t) (sextic s t).derivative)≠0 := by
  rw [←Polynomial.aeval_algHom_apply,ev_x,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id,derivative_eq]
  exact hs
theorem local_read (s t α : k) (h : eqVal s t α=0) (hs : derVal s t α≠0)
    (G : Polynomial k) (i j : ℕ) :
    let φ:=ev s t α h
    specialize φ (principalNumerator φ (x₀ s t) (sextic s t) G i j (unit_jac s t α h hs)) =
      -2*α^(i+j)*G.eval α/(derVal s t α)^2 := by
  dsimp only
  rw [principal_read,ev_x,derivative_eq]
end OriginalSparseActualBranch318
#print axioms OriginalSparseActualBranch318.branch_uniformizer
#print axioms OriginalSparseActualBranch318.local_read
