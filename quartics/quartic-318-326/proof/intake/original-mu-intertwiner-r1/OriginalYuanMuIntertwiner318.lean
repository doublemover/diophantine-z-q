module
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.Ring
public section
namespace OriginalYuanMuIntertwiner318
abbrev Mat (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- For a genuine generic action of the full matrix algebra twisted by
X ↦ m⁻¹ X m, the intertwiners are precisely the line of m, not merely
a rank-one subspace whose generator could be unrelated to μ. -/
theorem generic_eq_smul {K : Type*} [Field K] (m : (Mat K)ˣ) (F : Mat K)
    (hF : ∀ X : Mat K, F * ((↑m⁻¹ : Mat K) * X * (m : Mat K)) = X * F) :
    ∃ c : K, F = c • (m : Mat K) := by
  have hcent (X : Mat K) : Commute X (F * (↑m⁻¹ : Mat K)) := by
    have h := congrArg (fun A : Mat K => A * (↑m⁻¹ : Mat K)) (hF X)
    change X * (F * (↑m⁻¹ : Mat K)) = (F * (↑m⁻¹ : Mat K)) * X
    simpa only [mul_assoc, Units.mul_inv, mul_one] using h.symm
  obtain ⟨c,hc⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := F * (↑m⁻¹ : Mat K)) (fun i j _ => hcent (Matrix.single i j 1))
  refine ⟨c,?_⟩
  calc
    F = (F * (↑m⁻¹ : Mat K)) * (m : Mat K) := by rw [mul_assoc,Units.inv_mul,mul_one]
    _ = Matrix.scalar (Fin 2) c * (m : Mat K) := by rw [hc]
    _ = c • (m : Mat K) := (Matrix.smul_eq_diagonal_mul (m : Mat K) c).symm

/-- Conversely every multiple of this same m intertwines the prescribed
twisted action. This direction does not select a frame of the Hom line. -/
theorem generic_smul_intertwines {K : Type*} [Field K] (m : (Mat K)ˣ)
    (c : K) (X : Mat K) :
    (c • (m : Mat K)) * ((↑m⁻¹ : Mat K)*X*(m : Mat K)) = X * (c • (m : Mat K)) := by
  rw [smul_mul_assoc,mul_smul_comm]
  congr 1
  calc
    (m : Mat K) * ((↑m⁻¹ : Mat K) * X * (m : Mat K)) =
        ((m : Mat K) * (↑m⁻¹ : Mat K)) * (X * (m : Mat K)) := by simp only [mul_assoc]
    _ = X * (m : Mat K) := by rw [Units.mul_inv,one_mul]

/-- An integral 2×2 determinant with valuation at most one forces an
actual unit entry in a local chart. No unramified splitting basis. -/
theorem unit_entry {R : Type*} [CommRing R] [IsLocalRing R] (M : Mat R)
    (h : M.det ∉ (IsLocalRing.maximalIdeal R)^2) :
    ∃ i j, IsUnit (M i j) := by
  classical
  by_contra hn
  have hm (i j : Fin 2) : M i j ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal _).2 (fun hu => hn ⟨i,j,hu⟩)
  apply h
  rw [Matrix.det_fin_two,pow_two]
  exact Ideal.sub_mem _ (Ideal.mul_mem_mul (hm 0 0) (hm 1 1))
    (Ideal.mul_mem_mul (hm 0 1) (hm 1 0))

/-- Structural reduced special fibre controls the multiplicity of d.
A nonzero generator of a reduced principal quotient in a DVR is a
unit or an irreducible. This also permits horizontal points. -/
theorem unit_or_irreducible_of_reduced {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (d : R) (hd : d ≠ 0)
    [IsReduced (R ⧸ Ideal.span ({d} : Set R))] : IsUnit d ∨ Irreducible d := by
  classical
  by_cases hu : IsUnit d
  · exact Or.inl hu
  right
  let I := Ideal.span ({d} : Set R)
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n,u,he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
  have hm : π^n ∈ I := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(↑(u⁻¹) : R), ?_⟩
    calc
      π^n = ((u : R) * (↑(u⁻¹) : R)) * π^n := by rw [Units.mul_inv,one_mul]
      _ = ((u : R) * π^n) * (↑(u⁻¹) : R) := by ring
      _ = d * (↑(u⁻¹) : R) := by rw [he]
  have hnil : IsNilpotent (Ideal.Quotient.mk I π) :=
    ⟨n,by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hm⟩
  have hmem : π ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (isNilpotent_iff_eq_zero.mp hnil)
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨hu,?_⟩
  intro x y hxy
  have hfac : π = x * (y * b) := by rw [hb,hxy,mul_assoc]
  rcases hπ.isUnit_or_isUnit hfac with hx | hy
  · exact Or.inl hx
  · exact Or.inr ((IsUnit.mul_iff.mp hy).1)

theorem not_mem_square {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : R} (hd : IsUnit d ∨ Irreducible d) : d ∉ (IsLocalRing.maximalIdeal R)^2 := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  intro hm
  rw [hπ.maximalIdeal_eq,Ideal.span_singleton_pow] at hm
  obtain ⟨v,hv⟩ := Ideal.mem_span_singleton.mp hm
  have e : d = π * (π * v) := hv.trans (by ring)
  rcases hd with hu | hi
  · rw [e] at hu
    exact hπ.not_isUnit ((IsUnit.mul_iff.mp hu).1)
  · rcases hi.isUnit_or_isUnit e with hp | hpv
    · exact hπ.not_isUnit hp
    · exact hπ.not_isUnit ((IsUnit.mul_iff.mp hpv).1)

/-- Descent from the actual generic scalar uses a unit ENTRY of μ, not
integrality of the chosen generic scalar as an extra hypothesis. -/
theorem scalar_back {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Injective f) (F M : Mat R) (c : K)
    (hunit : ∃ i j, IsUnit (M i j)) (hF : F.map f = c • M.map f) :
    ∃ z : R, F = z • M := by
  obtain ⟨i,j,a,ha⟩ := hunit
  have he (k l : Fin 2) : f (F k l) = c * f (M k l) :=
    congrArg (fun B : Mat K => B k l) hF
  let z := F i j * (↑(a⁻¹) : R)
  have hz : f z = c := by
    change f (F i j * (↑(a⁻¹) : R)) = c
    rw [map_mul,he,← ha,mul_assoc,← map_mul,Units.mul_inv,map_one,mul_one]
  refine ⟨z,Matrix.ext fun k l => hf ?_⟩
  change f (F k l) = f (z * M k l)
  rw [map_mul,hz,he]

/-- Structural-DVR cyclicity for the same μ, including p=2.  The unit
m carries the literal generic image of the integral μ matrix.  In the PEL
application det M=210 and M⁻¹ conjugation equals M conjugation, since
μ²=−210; semistable structural reducedness is used *before* any trait pullback. -/
theorem original_intertwiner_cyclic {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (F M : Mat R) (m : (Mat K)ˣ) (hm : (m : Mat K) = M.map f)
    (hd : M.det ≠ 0) [IsReduced (R ⧸ Ideal.span ({M.det} : Set R))]
    (hF : ∀ X : Mat K,
      F.map f * ((↑m⁻¹ : Mat K)*X*(m : Mat K)) = X * F.map f) :
    ∃ z : R, F = z • M := by
  obtain ⟨c,hc⟩ := generic_eq_smul m (F.map f) hF
  rw [hm] at hc
  exact scalar_back f hf F M c
    (unit_entry M (not_mem_square (unit_or_irreducible_of_reduced M.det hd))) hc

/-- Form the generic unit from the actual matrix, without postulating a
generic unit or a centralizer dimension. The determinant of *each*
integral intertwiner is the square of its scalar times the specified d. -/
theorem cyclic_and_determinant {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (F M : Mat R) (hd : M.det ≠ 0) [IsReduced (R ⧸ Ideal.span ({M.det} : Set R))]
    (hF : ∀ X : Mat K, F.map f * ((M.map f)⁻¹ * X * M.map f) = X * F.map f) :
    ∃ z : R, F = z • M ∧ F.det = z^2 * M.det := by
  have hdet : (M.map f).det ≠ 0 := by
    intro h
    apply hd
    apply hf
    rw [map_zero]
    exact (f.map_det M).trans h
  let m := Matrix.GeneralLinearGroup.mkOfDetNeZero (M.map f) hdet
  have hm : (m : Mat K) = M.map f := rfl
  have hi : (↑m⁻¹ : Mat K) = (M.map f)⁻¹ := Matrix.GeneralLinearGroup.coe_inv m
  obtain ⟨z,hz⟩ := original_intertwiner_cyclic f hf F M m hm hd
    (fun X => by simpa only [hi,hm] using hF X)
  exact ⟨z,hz,by rw [hz,Matrix.det_smul,Fintype.card_fin]⟩

end OriginalYuanMuIntertwiner318
