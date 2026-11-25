module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
Original split-f-eigenframe computation of the polarized KS
intertwiner. This is valid at residue characteristic 2 without dividing
by 2; the spectral gap u-v is a unit. The Rosati-derived source
representation has f'=1-f, g'=-g for the literal original mu=g(2f-1).
-/
@[expose] public section

namespace OriginalDyadicYuanIntertwiner318

abbrev Mat (R : Type*) := Matrix (Fin 2) (Fin 2) R

variable {R : Type*} [CommRing R]

def diag (u v : R) : Mat R := !![u, 0; 0, v]
def switch (a b : R) : Mat R := !![0, b; a, 0]

/-- This is the left Lie action of mu=g*j, not j*g. -/
def mu (w a b : R) : Mat R := !![0, -(b*w); a*w, 0]

def intertwines (u v a b : R) (M : Mat R) : Prop :=
  M * diag v u = diag u v * M ∧ M * switch (-a) (-b) = switch a b * M

theorem directed_mu (w a b : R) : switch a b * diag w (-w) = mu w a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag, switch, mu, Matrix.mul_apply, Fin.sum_univ_two]

theorem mu_intertwines (u v w a b : R) : intertwines u v a b (mu w a b) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diag, switch, mu, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem scalar_pair (a b w x y : R) (hw : IsUnit w)
    (hab : IsUnit a ∨ IsUnit b) (rel : a*x+b*y=0) :
    ∃! c : R, x = c * (-(b*w)) ∧ y = c * (a*w) := by
  rcases hab with ha | hb
  · obtain ⟨U,hU⟩ := ha.mul hw
    have hUU : (↑U : R) = a*w := hU
    let c : R := y * (↑U⁻¹ : R)
    have cy : c*(a*w)=y := by rw [← hUU]; simp [c, mul_assoc]
    have cx : x=c*(-(b*w)) := by
      apply ha.mul_left_cancel
      linear_combination rel + b*cy
    refine ⟨c,⟨cx,cy.symm⟩,?_⟩
    intro e he
    exact (ha.mul hw).mul_right_cancel (he.2.symm.trans cy.symm)
  · obtain ⟨U,hU⟩ := (hb.mul hw).neg
    have hUU : (↑U : R) = -(b*w) := hU
    let c : R := x * (↑U⁻¹ : R)
    have cx : c*(-(b*w))=x := by rw [← hUU]; simp [c, mul_assoc]
    have cy : y=c*(a*w) := by
      apply hb.mul_left_cancel
      linear_combination rel + a*cx
    refine ⟨c,⟨cx.symm,cy⟩,?_⟩
    intro e he
    exact (hb.mul hw).neg.mul_right_cancel (he.1.symm.trans cx.symm)

/-- The integral intertwiner line is exactly the span of the named mu.
A unit entry, not a generic scalar extension argument alone, proves every
integral intertwiner has integral coefficient. -/
theorem exact_intertwiners (u v a b : R) (gap : IsUnit (u-v))
    (entry : IsUnit a ∨ IsUnit b) (M : Mat R) (h : intertwines u v a b M) :
    ∃! c : R, M = c • mu (u-v) a b := by
  have lf₀ := congrArg (fun Q : Mat R => Q 0 0) h.1
  have lf₁ := congrArg (fun Q : Mat R => Q 1 1) h.1
  have lg := congrArg (fun Q : Mat R => Q 0 0) h.2
  simp [diag, switch, Matrix.mul_apply, Fin.sum_univ_two] at lf₀ lf₁ lg
  have z₀ : M 0 0 = 0 := by
    apply gap.mul_right_cancel
    linear_combination -lf₀
  have z₁ : M 1 1 = 0 := by
    apply gap.mul_right_cancel
    linear_combination lf₁
  have rel : a * M 0 1 + b * M 1 0 = 0 := by linear_combination -lg
  obtain ⟨c,hc,huniq⟩ := scalar_pair a b (u-v) (M 0 1) (M 1 0) gap entry rel
  refine ⟨c, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · change M 0 0 = c * 0
      simpa using z₀
    · exact hc.1
    · exact hc.2
    · change M 1 1 = c * 0
      simpa using z₁
  · intro e he
    apply huniq
    exact ⟨congrArg (fun Q : Mat R => Q 0 1) he,
      congrArg (fun Q : Mat R => Q 1 0) he⟩

/-- Determinant of the literal mu-scale, with a signed order control. -/
theorem determinant (w a b c : R) :
    Matrix.det (c • mu w a b) = c^2 * (a*b) * w^2 := by
  rw [Matrix.det_fin_two]
  change (c*0)*(c*0) - (c*(-(b*w)))*(c*(a*w)) = _
  ring

/-- A genuine KS generator is a *unit* multiple of the actual mu.
The preimage q here is its existence read from the geometric iso
onto the full O-linear Hom line, not merely from det(KS) nonzero. -/
theorem unit_generator (u v a b : R) (gap : IsUnit (u-v))
    (entry : IsUnit a ∨ IsUnit b) (M : Mat R) (h : intertwines u v a b M)
    (onto : ∃ q : R, q • M = mu (u-v) a b) :
    ∃ c : R, IsUnit c ∧ M = c • mu (u-v) a b := by
  obtain ⟨c,hc,_⟩ := exact_intertwiners u v a b gap entry M h
  obtain ⟨q,hq⟩ := onto
  obtain ⟨_,_,uniq⟩ := exact_intertwiners u v a b gap entry (mu (u-v) a b)
    (mu_intertwines u v (u-v) a b)
  have e : mu (u-v) a b = (q*c) • mu (u-v) a b := by
    rw [← smul_smul, ← hc]
    exact hq.symm
  have e1 : mu (u-v) a b = (1:R) • mu (u-v) a b := (one_smul _ _).symm
  have qc : q*c=1 := (uniq (q*c) e).trans (uniq 1 e1).symm
  exact ⟨c,isUnit_iff_exists_inv.mpr ⟨q,by rw [mul_comm, qc]⟩,hc⟩

/-- On the original f-split structural component at p=2 (also 3,7)
the exact determinant coefficient is 210 times a unit square, in
the actual Rosati/KS Lie source convention. -/
theorem original_dyadic (u v a b : R) (sumroots : u+v=1) (prodroots : u*v= -1)
    (gap : IsUnit (u-v)) (prod : a*b=42) (structural : Irreducible (42:R))
    (M : Mat R) (h : intertwines u v a b M)
    (geometricKS : ∃ q : R, q • M = mu (u-v) a b) :
    ∃ c : R, IsUnit c ∧ M = c • mu (u-v) a b ∧ Matrix.det M = 210*c^2 := by
  have e : (u-v)^2=5 := by linear_combination (u+v+1)*sumroots - 4*prodroots
  obtain ⟨c,hc,hMc⟩ := unit_generator u v a b gap
    (structural.isUnit_or_isUnit prod.symm) M h geometricKS
  refine ⟨c,hc,hMc,?_⟩
  rw [hMc,determinant,prod,e]
  ring

end OriginalDyadicYuanIntertwiner318

#print axioms OriginalDyadicYuanIntertwiner318.directed_mu
#print axioms OriginalDyadicYuanIntertwiner318.exact_intertwiners
#print axioms OriginalDyadicYuanIntertwiner318.original_dyadic
