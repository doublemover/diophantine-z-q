module
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section

namespace ActualGaussianComplexTorusKernel318

abbrev iota : GaussianInt →+* ℂ := GaussianInt.toComplex

/-- The literal square-period lattice, with the positive complex
embedding, not an abstract prescribed finite kernel. -/
abbrev lattice : AddSubgroup ℂ := iota.toAddMonoidHom.range

abbrev Torus := ℂ ⧸ lattice

abbrev V : ℂ →+ Torus := QuotientAddGroup.mk' lattice

private def scaled (a : GaussianInt) : ℂ →+ Torus :=
  V.comp
    { toFun := fun x => iota a*x
      map_zero' := mul_zero _
      map_add' := mul_add _ }

private theorem scaled_kills (a : GaussianInt) : lattice ≤ (scaled a).ker := by
  rintro _ ⟨z,rfl⟩
  apply AddMonoidHom.mem_ker.mpr
  change V (iota a*iota z)=0
  rw [←map_mul]
  exact (QuotientAddGroup.eq_zero_iff (N:=lattice) _).mpr ⟨a*z,rfl⟩

/-- Actual scalar multiplication on the fixed analytic torus
before relating the torus to the elliptic curve. -/
def scalar (a : GaussianInt) : Torus →+ Torus :=
  QuotientAddGroup.lift lattice (scaled a) (scaled_kills a)

theorem scalar_on (a : GaussianInt) (x : ℂ) : scalar a (V x)=V (iota a*x) := by
  unfold scalar
  have h := DFunLike.congr_fun
    (QuotientAddGroup.lift_comp_mk' lattice (scaled a) (scaled_kills a)) x
  change (QuotientAddGroup.lift lattice (scaled a) (scaled_kills a)) (V x) =
    (scaled a) x at h
  exact h.trans (show (scaled a) x = V (iota a*x) from rfl)

end ActualGaussianComplexTorusKernel318
