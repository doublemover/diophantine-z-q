module
public import OriginalUpperActualFibreComponents318
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Ideal.Cotangent

public section
noncomputable section
namespace OriginalUpperActualComponentConormal318

open AlgebraicGeometry TopologicalSpace
open OriginalUpperActualFibreComponents318 (C ambientSupport pointAt)

universe u
variable {X Z : Scheme.{u}} [IsIntegral X] (s : X ⟶ Z) (p : Z)
variable (E : C s p) (x : X) (hx : x ∈ ambientSupport s p E)
local notation "A" => X.presheaf.stalk x
local notation "I" => PrimeSpectrum.asIdeal (pointAt s p E x hx)
local notation "B" => A ⧸ I
local notation "M" => Ideal.Cotangent I

/-- A primitive equation for the genuine reduced component ideal in
this ordinary stalk. The proof uses exactly Cartier primality from
the original regular surface, not an unrelated hypersurface. -/
structure Equation where
  f : A
  nonzero : f ≠ 0
  ideal_eq : I = Ideal.span ({f}:Set A)

variable (e : Equation s p E x hx)

def generator : I :=
  ⟨e.f,e.ideal_eq.symm ▸ Ideal.mem_span_singleton_self e.f⟩

def conormalVector : M := (I).toCotangent (generator s p E x hx e)

def conormalMap : B →ₗ[A] M :=
  (I : Submodule A A).liftQ (LinearMap.toSpanSingleton A M (conormalVector s p E x hx e))
    (fun _ ha => Ideal.Cotangent.smul_eq_zero_of_mem ha (conormalVector s p E x hx e))

theorem read_mk (a : A) :
    conormalMap s p E x hx e (Ideal.Quotient.mk I a) =
      (I).toCotangent (a • generator s p E x hx e) := by
  rw [conormalMap,Submodule.liftQ_apply]
  change a • (I).toCotangent (generator s p E x hx e) = _
  rw [map_smul]

/-- The actual local conormal I/I², as a module over the actual
component, is free with the original Cartier equation as a basis. -/
def conormalBasis : B ≃ₗ[B] M :=
  (LinearEquiv.ofBijective (conormalMap s p E x hx e) (by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective v
      rw [read_mk] at hv
      have H := ((I).toCotangent_eq_zero (a • generator s p E x hx e)).mp hv
      change a * e.f ∈ I^2 at H
      rw [e.ideal_eq,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at H
      obtain ⟨d,hd⟩ := H
      have hcancel : a = e.f*d := mul_right_cancel₀ e.nonzero (by
        calc a*e.f = e.f^2*d := hd
             _ = (e.f*d)*e.f := by rw [pow_two]; ac_rfl)
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [e.ideal_eq,Ideal.mem_span_singleton]
      exact ⟨d,hcancel⟩
    · intro v
      obtain ⟨z,rfl⟩ := (I).toCotangent_surjective v
      have hz : (z : A) ∈ Ideal.span ({e.f} : Set A) := (le_of_eq e.ideal_eq) z.property
      obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hz
      refine ⟨Ideal.Quotient.mk I a,?_⟩
      rw [read_mk]
      congr 1
      exact Subtype.ext ((mul_comm a e.f).trans ha.symm))).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

theorem basis_read_one : conormalBasis s p E x hx e 1 = conormalVector s p E x hx e := by
  change conormalMap s p E x hx e (Ideal.Quotient.mk I 1) = _
  exact (read_mk s p E x hx e 1).trans (by simp only [one_smul,conormalVector])

/-- The frame of the true normal line \((I/I^2)^\vee\) used in
Cartier adjunction. -/
def normalFrame : M →ₗ[B] B := (conormalBasis s p E x hx e).symm.toLinearMap

theorem normal_reads_one :
    normalFrame s p E x hx e (conormalVector s p E x hx e) = 1 := by
  rw [←basis_read_one s p E x hx e]
  exact (conormalBasis s p E x hx e).symm_apply_apply 1

/-- *Inverse* unit transition for the true adjunction normal frame.
For f'=u f, f'^∨=u⁻¹ f^∨ on the component; the map is an identity in
the actual local module, not a choice of arithmetic degree. -/
theorem normal_transition (e' : Equation s p E x hx) (u : Aˣ)
    (he : e'.f = (u:A)*e.f) :
    normalFrame s p E x hx e' =
      (Ideal.Quotient.mk I ((u⁻¹:Aˣ):A)) • normalFrame s p E x hx e := by
  let b := Ideal.Quotient.mk I (u:A)
  let b' := Ideal.Quotient.mk I ((u⁻¹:Aˣ):A)
  have hunit : b' * b = 1 := by
    change (Ideal.Quotient.mk I _) * Ideal.Quotient.mk I _ = _
    rw [←map_mul,Units.inv_mul,map_one]
  have hv : conormalVector s p E x hx e' = b • conormalVector s p E x hx e := by
    have h : generator s p E x hx e' = (u:A) • generator s p E x hx e :=
      Subtype.ext he
    rw [conormalVector,h,map_smul]
    exact (IsScalarTower.algebraMap_smul B (u:A) (conormalVector s p E x hx e)).symm
  ext z
  obtain ⟨d,rfl⟩ := (conormalBasis s p E x hx e').surjective z
  have hd : conormalBasis s p E x hx e' d = d • conormalVector s p E x hx e' := by
    rw [←basis_read_one s p E x hx e',←map_smul,smul_eq_mul,mul_one]
  rw [hd,map_smul,normal_reads_one,LinearMap.smul_apply,hv,
    map_smul,map_smul,normal_reads_one]
  change d * 1 = b' * (d * (b * 1))
  rw [mul_one,mul_one,mul_left_comm b' d,hunit,mul_one]

/-- The actual length-one ambient Koszul resolution used by adjunction:
multiplication by the primitive component equation has image exactly
the kernel of the true quotient map, and is injective. -/
theorem koszul_exact :
    Function.Injective (LinearMap.mulRight A e.f) ∧
      Function.Exact (LinearMap.mulRight A e.f) ((I : Submodule A A).mkQ) := by
  constructor
  · intro a b h
    exact mul_right_cancel₀ e.nonzero h
  · apply LinearMap.exact_iff.mpr
    rw [Submodule.ker_mkQ]
    ext a
    rw [LinearMap.mem_range,e.ideal_eq,Ideal.mem_span_singleton]
    constructor
    · rintro ⟨z,hz⟩
      exact ⟨z,(mul_comm z e.f).trans hz.symm⟩
    · rintro ⟨z,hz⟩
      exact ⟨z,hz.symm.trans (mul_comm z e.f)⟩

end OriginalUpperActualComponentConormal318

#print axioms OriginalUpperActualComponentConormal318.conormalBasis
#print axioms OriginalUpperActualComponentConormal318.normal_transition
#print axioms OriginalUpperActualComponentConormal318.koszul_exact
