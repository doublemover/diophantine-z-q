module
public import Height13RealLog
public import Mathlib.Data.ZMod.Basic
public section
namespace AnchorLocalCharts
variable {F : Type*} [Field F]

def q (x y z : F) : F := x^2+6*y^2-2*z^2

/-- Unit case at 2, and every case at 3. -/
theorem square_chart (r s : F) (hs : s^2=3*r^2-2) :
    q s 0 0=3*r^2-2 := by simpa [q] using hs

/-- The v₂(r)=1 chart, with r=2k and k a unit. -/
theorem valuation_one_chart (k s : F) (hs : s^2=3*k^2-2) :
    q (2*s) 1 0=3*(2*k)^2-2 := by
  dsimp [q]
  linear_combination 4*hs

/-- The r∈4Z₂ chart, including r=0. -/
theorem divisible_four_chart (k s : F) (hs : s^2=1+8*k^2) :
    q 0 s 2=3*(4*k)^2-2 := by
  dsimp [q]
  linear_combination 6*hs

/-- Finite residue computation behind both odd-unit square-root tests at 2. -/
theorem odd_radicand_mod_eight : ∀ k : ZMod 8,
    k.val % 2=1 → 3*k^2-2=1 := by decide

theorem deep_radicand_mod_eight : ∀ k : ZMod 8,
    1+8*k^2=1 := by decide

theorem radicand_mod_three : ∀ r : ZMod 3,
    3*r^2-2=1 := by decide

/-- The global isotropic vector's affine denominator is forced nonzero by
anisotropy of the ternary subform. The local Q₃ argument supplying anisotropy
is recorded in ANCHOR-COMPLETENESS.md, not silently assumed as a library fact. -/
theorem homogeneous_denominator_nonzero (c X Y Z T : F)
    (hanis : ∀ x y z : F, q x y z=0 → x=0 ∧ y=0 ∧ z=0)
    (hQ : q X Y Z=c*T^2)
    (hnonzero : ¬(X=0 ∧ Y=0 ∧ Z=0 ∧ T=0)) : T≠0 := by
  intro hT
  have hzero : q X Y Z=0 := by simpa [hT] using hQ
  obtain ⟨hX,hY,hZ⟩ := hanis X Y Z hzero
  exact hnonzero ⟨hX,hY,hZ,hT⟩

theorem homogeneous_to_affine (c X Y Z T : F) (hT : T≠0)
    (hQ : q X Y Z=c*T^2) : q (X/T) (Y/T) (Z/T)=c := by
  dsimp [q] at *
  field_simp
  simpa [mul_comm] using hQ

/-- Scaling back gives the literal unsheared physical-anchor polynomial. -/
theorem physical_scaling (A S x y z : F) (hS : S≠0)
    (hrep : q x y z=3*(A/S)^2-2) :
    (S*x)^2+6*(S*y)^2-2*(S*z)^2-3*A^2+2*S^2=0 := by
  dsimp [q] at hrep
  field_simp at hrep
  linear_combination hrep

#print axioms odd_radicand_mod_eight
#print axioms homogeneous_denominator_nonzero
#print axioms homogeneous_to_affine
#print axioms physical_scaling
end AnchorLocalCharts
