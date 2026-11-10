module
public import PELOriginalLocalAlgebraClassification318
public section
noncomputable section
namespace PELOriginalOrderNonescape318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
open PELPrincipalOrderCoordinates318 PELOriginalRamifiedDivision318
set_option maxHeartbeats 1400000
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

/-- The ORIGINAL real period representation has the actual integer norm
as determinant on the specified maximal order. -/
theorem order_det (x : order) : (representation (x:B)).det=(orderNorm x:ℝ) := by
  have h : (representation (x:B)).det=(reducedNorm (x:B):ℝ) := by
    simp only [representation,matrix,Matrix.det_fin_two,Matrix.cons_val_zero,
      Matrix.cons_val_one,reducedNorm]
    push_cast
    ring_nf
    simp only [alpha_sq,beta_sq] <;> ring
  rw [orderNorm_value] at h
  exact_mod_cast h

theorem orderNorm_ne_zero (x : order) (hx : x≠0) : orderNorm x≠0 := by
  have hv : (x:B)≠0 := by
    intro h
    exact hx (Subtype.ext h)
  intro h
  apply PELQuaternionAnisotropy318.reducedNorm_ne_zero (x:B) hv
  rw [orderNorm_value,h,Int.cast_zero]

theorem determinant_lower (x : order) (hx : x≠0) (g : Mat) (hg : g.det=1) :
    1≤|(representation (x:B)*g).det| := by
  rw [Matrix.det_mul,hg,mul_one,order_det]
  exact_mod_cast Int.one_le_abs (orderNorm_ne_zero x hx)

theorem small_entries_small_det (M : Mat) (h : ∀ i j,|M i j|<(1/2:ℝ)) :
    |M.det|<1 := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  have hdiag : |M 0 0|*|M 1 1|<1/4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h00.le) (abs_nonneg (M 1 1))]
  have hoff : |M 0 1|*|M 1 0|<1/4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h01.le) (abs_nonneg (M 1 0))]
  rw [Matrix.det_fin_two]
  have ht := abs_sub_le (M 0 0*M 1 1) (M 0 1*M 1 0)
  rw [abs_mul,abs_mul] at ht
  linarith

/-- A fixed lower bound valid for EVERY nonzero original-order element
and EVERY determinant-one real transport, not just a fixed compact family. -/
theorem entry_lower (x : order) (hx : x≠0) (g : Mat) (hg : g.det=1) :
    ∃ i j : Fin 2, (1/2:ℝ)≤|(representation (x:B)*g) i j| := by
  by_contra h
  push_neg at h
  exact (not_lt_of_ge (determinant_lower x hx g hg)) (small_entries_small_det _ h)

@[expose] def rightMap (g : Mat) : order →+ Mat where
  toFun x := representation (x:B)*g
  map_zero' := by simp
  map_add' x y := by simp [add_mul]

/-- The literal right-transported original order, rather than an unrelated
lattice chosen from its rank or covolume. -/
@[expose] def lattice (g : Mat) : AddSubgroup Mat := (rightMap g).range

theorem lattice_entry_lower (g : Mat) (hg : g.det=1) (M : Mat)
    (hM : M∈lattice g) (hne : M≠0) : ∃ i j : Fin 2, (1/2:ℝ)≤|M i j| := by
  obtain ⟨x,rfl⟩ := hM
  have hx : x≠0 := by
    intro hx
    exact hne (by simp [hx])
  exact entry_lower x hx g hg

/-- The same explicit neighborhood of0 contains no nonzero member of ANY
determinant-one transported original order. -/
theorem uniform_zero_neighborhood (g : Mat) (hg : g.det=1) (M : Mat)
    (hM : M∈lattice g) (hsmall : ∀ i j,|M i j|<(1/2:ℝ)) : M=0 := by
  by_contra hne
  obtain ⟨i,j,hij⟩ := lattice_entry_lower g hg M hM hne
  exact (not_lt_of_ge hij) (hsmall i j)

@[expose] def smallBox : Set Mat := {M | ∀ i j,|M i j|<(1/2:ℝ)}

theorem smallBox_open : IsOpen smallBox := by
  change IsOpen (⋂ i : Fin 2, ⋂ j : Fin 2, {M : Mat | |M i j|<(1/2:ℝ)})
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (((continuous_apply j).comp (continuous_apply i)).abs) continuous_const

theorem zero_mem_smallBox : (0:Mat)∈smallBox := by
  intro i j
  norm_num

theorem lattice_smallBox (g : Mat) (hg : g.det=1) :
    (lattice g : Set Mat) ∩ smallBox={0} := by
  ext M
  constructor
  · intro h
    exact uniform_zero_neighborhood g hg M h.1 h.2
  · intro h
    have hM : M=0 := h
    subst M
    exact ⟨(lattice g).zero_mem,zero_mem_smallBox⟩

theorem rightMap_unit (u : orderˣ) (g : Mat) (x : order) :
    rightMap (representation ((u:order):B)*g) x=rightMap g (x*(u:order)) := by
  change representation (x:B)*(representation ((u:order):B)*g)=
    representation ((x: B)*((u:order):B))*g
  rw [map_mul,mul_assoc]

/-- Actual quotient invariance: left multiplication by ANY original order
unit leaves the entire right-transported lattice unchanged. In particular
the norm-one group acting on the real symmetric space preserves this datum. -/
theorem lattice_unit (u : orderˣ) (g : Mat) :
    lattice (representation ((u:order):B)*g)=lattice g := by
  ext M
  change (∃ x,rightMap (representation ((u:order):B)*g) x=M) ↔ ∃ x,rightMap g x=M
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x*(u:order),(rightMap_unit u g x).symm⟩
  · rintro ⟨x,rfl⟩
    refine ⟨x*((u⁻¹:orderˣ):order),?_⟩
    rw [rightMap_unit]
    simp [mul_assoc]
end PELOriginalOrderNonescape318
