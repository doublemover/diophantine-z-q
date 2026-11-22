module
public import PointwiseConverseRetainedArtinRows
public import PointwiseConverseRawMatrixReconstruction
import all PointwiseConverseRawMatrixReconstruction
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open PointwiseConverseRetainedArtinRows PointwiseConverseRawMatrixReceiver
open PointwiseConverseRawMatrixReconstruction

namespace PointwiseConverseArtinRingCut

abbrev Lambda := PowerSeries (PadicInt 2)
abbrev representative (i : ℕ) := AdjoinRoot.modByMonicHom (monic_rel i)

/-- Reduction by X^i does not change any coefficient below i. The
proof uses division with remainder over ZMod(2^i), not a field. -/
theorem coeff_mk (i : ℕ) (p : Polynomial (C i)) (d : Fin i) :
    coeff i (AdjoinRoot.mk (rel i) p) d = p.coeff d.val := by
  have hzero (Q : Polynomial (C i)) : ((rel i)*Q).coeff d.val = 0 := by
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro a ha
    have hdeg := Finset.mem_antidiagonal.mp ha
    have hne : a.1 ≠ i := by omega
    simp [rel,Polynomial.coeff_X_pow,hne]
  have h := congrArg (fun f : Polynomial (C i) => f.coeff d.val)
    (Polynomial.modByMonic_add_div p (rel i))
  rw [Polynomial.coeff_add,hzero,add_zero] at h
  simpa only [coeff,AdjoinRoot.modByMonicHom_mk] using h

/-- Convolution on the actual quotient ring; since the sum is over the
antidiagonal of d<i, the displayed factors are all genuinely retained. -/
theorem coeff_mul (i : ℕ) (a b : A i) (d : Fin i) :
    coeff i (a*b) d = ∑ z ∈ Finset.antidiagonal d.val,
      (representative i a).coeff z.1 * (representative i b).coeff z.2 := by
  have e : AdjoinRoot.mk (rel i) ((representative i a)*(representative i b)) = a*b := by
    rw [map_mul,AdjoinRoot.mk_leftInverse (monic_rel i) a,AdjoinRoot.mk_leftInverse (monic_rel i) b]
  rw [←e,coeff_mk,Polynomial.coeff_mul]

def ofCoeffs (i : ℕ) (v : Fin i → C i) : A i :=
  AdjoinRoot.mk (rel i) (∑ k : Fin i, Polynomial.monomial k.val (v k))

theorem coeff_ofCoeffs (i : ℕ) (v : Fin i → C i) (d : Fin i) :
    coeff i (ofCoeffs i v) d = v d := by
  classical
  rw [ofCoeffs, coeff_mk, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hbd
    have e : b.val ≠ d.val := fun h => hbd (Fin.ext h)
    simp [Polynomial.coeff_monomial,e]
  · simp

def raw (i : ℕ) (x : Lambda) (d : Fin i) : C i :=
  PadicInt.toZModPow i (PowerSeries.coeff d.val x)

def projectSeries (i : ℕ) (x : Lambda) : A i := ofCoeffs i (raw i x)

theorem coeff_project (i : ℕ) (x : Lambda) (d : Fin i) :
    coeff i (projectSeries i x) d = raw i x d := coeff_ofCoeffs _ _ _

theorem project_mul (i : ℕ) (a b : Lambda) :
    projectSeries i (a*b) = projectSeries i a * projectSeries i b := by
  apply coeff_injective
  funext d
  rw [coeff_project,coeff_mul]
  unfold raw
  rw [PowerSeries.coeff_mul,map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hdeg := Finset.mem_antidiagonal.mp hz
  have h1 : z.1 < i := by omega
  have h2 : z.2 < i := by omega
  have e1 := coeff_project i a ⟨z.1,h1⟩
  have e2 := coeff_project i b ⟨z.2,h2⟩
  change (representative i (projectSeries i a)).coeff z.1 = _ at e1
  change (representative i (projectSeries i b)).coeff z.2 = _ at e2
  rw [e1,e2,map_mul]
  rfl

/-- Honest ring hom in the safe direction: full Λ to its finite Artin
cut. There is deliberately no arrow from A_i to the t-inverted target. -/
def cutHom (i : ℕ) : Lambda →+* A i where
  toFun := projectSeries i
  map_mul' := project_mul i
  map_zero' := by
    apply coeff_injective
    funext d
    rw [coeff_project]
    change PadicInt.toZModPow i (PowerSeries.coeff d.val (0 : Lambda)) =
      (representative i (0 : A i)).coeff d.val
    simp only [map_zero,Polynomial.coeff_zero]
    rfl
  map_one' := by
    apply coeff_injective
    funext d
    calc coeff i (projectSeries i 1) d = raw i 1 d := coeff_project _ _ _
         _ = (1 : Polynomial (C i)).coeff d.val := by
           classical
           by_cases h : d.val = 0 <;>
             simp [raw,PowerSeries.coeff_one,Polynomial.coeff_one,h]
           all_goals rfl
         _ = coeff i (1 : A i) d := by
           simpa only [map_one] using (coeff_mk i (1 : Polynomial (C i)) d).symm
  map_add' a b := by
    apply coeff_injective
    funext d
    rw [coeff_project]
    change PadicInt.toZModPow i (PowerSeries.coeff d.val (a+b)) =
      (representative i (projectSeries i a + projectSeries i b)).coeff d.val
    rw [map_add,map_add,map_add,Polynomial.coeff_add]
    exact congrArg₂ (·+·) (coeff_project i a d).symm (coeff_project i b d).symm

theorem as_raw_packet (S : Shape) (i : ℕ) (M : SeriesPacket S) :
    (fun m a b => coeff i (cutHom i (M m a b))) = cut S i M := by
  funext m a b d
  change coeff i (projectSeries i (M m a b)) d =
    PadicInt.toZModPow i (PowerSeries.coeff d.val (M m a b))
  exact coeff_project i (M m a b) d

/-- Polynomial matrix identities over full Λ descend along the original
Artin quotient map, before any height-one specialization. -/
theorem cut_matrix_mul {r s t : ℕ} (i : ℕ)
    (P : Matrix (Fin r) (Fin s) Lambda) (Q : Matrix (Fin s) (Fin t) Lambda) :
    (P*Q).map (cutHom i) = (P.map (cutHom i)) * (Q.map (cutHom i)) := by
  ext a b
  simp [Matrix.mul_apply,map_sum,map_mul]
end PointwiseConverseArtinRingCut
