module
public import OriginalSparseActualBranch318
public import OriginalBranchCechOverlap318
public section
noncomputable section
namespace OriginalActualCechLifts318
open Polynomial OriginalBranchCechCalculus318 OriginalUniversalSparsePolynomial318
open OriginalSparseActualBranch318
variable {k U : Type*} [Field k] [CommRing U] [Algebra k U]
theorem branch_hodge (F : k[X]) (x y yi ip : U) (hF : y^2=aeval x F) (hy : y*yi=1)
    (hp : aeval x F.derivative*ip=1) (i : ℕ) :
    (x^i*yi) • KaehlerDifferential.D k U x = (2*x^i*ip) • KaehlerDifferential.D k U y := by
  have h:=kahler F x y hF
  have hdx : KaehlerDifferential.D k U x = (ip*(2*y)) • KaehlerDifferential.D k U y := by
    rw [←smul_smul, h,smul_smul,mul_comm ip,hp,one_smul]
  rw [hdx,smul_smul]
  congr 1
  linear_combination (2*x^i*ip)*hy

/-- Two actual lifts on the affine plane quotient, functorially in every square-zero
test algebra of its punctured simple-branch chart. They solve the deformed equation
itself, not only a constraint on candidate branch velocities. -/
theorem on_actual (s t : k) (G : k[X]) (ρ : OriginalUniformSparseAffineModel318.Ring s t→ₐ[k]U)
    (ε iy ip : U) (hε : ε^2=0)
    (hi : (2*ρ (OriginalUniformSparseAffineModel318.y s t))*iy=1)
    (hp : aeval (ρ (OriginalUniformSparseAffineModel318.x s t)) (sextic s t).derivative*ip=1) :
    let x:=ρ (OriginalUniformSparseAffineModel318.x s t)
    let y:=ρ (OriginalUniformSparseAffineModel318.y s t)
    let g:=aeval x G
    (y+ε*(iy*g))^2=aeval x (sextic s t)+ε*g ∧
    y^2=aeval (x+ε*(-ip*g)) (sextic s t)+ε*aeval (x+ε*(-ip*g)) G ∧
    ∀ i : ℕ,(x^i*(2*iy)) • KaehlerDifferential.D k U x =
      (2*x^i*ip) • KaehlerDifferential.D k U y := by
  let x:=ρ (OriginalUniformSparseAffineModel318.x s t)
  let y:=ρ (OriginalUniformSparseAffineModel318.y s t)
  let g:=aeval x G
  have hy : y^2=aeval x (sextic s t) := by
    rw [aeval_algHom_apply ρ,← genuine s t,map_pow]
  obtain ⟨e0,e1,_⟩:=two_splittings y (aeval x (sextic s t).derivative) g iy ip hi hp
  refine ⟨?_,?_,?_⟩
  · simpa only [mul_zero,add_zero] using genuine_lift (sextic s t) G x y ε 0 (iy*g) hε hy e0
  · simpa only [mul_zero,add_zero] using genuine_lift (sextic s t) G x y ε (-ip*g) 0 hε hy e1
  · intro i
    apply branch_hodge _ _ _ _ _ hy _ hp
    linear_combination hi
end OriginalActualCechLifts318
#print axioms OriginalActualCechLifts318.on_actual
