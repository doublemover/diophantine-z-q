module
public import LevelThreeKernel318
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.LocalRing.Defs
public section
noncomputable section
namespace RamifiedResidueModel318
open LevelThreeKernel318 Matrix
set_option maxHeartbeats 0

/-- Frobenius on the literal field of nine elements. -/
abbrev σ : Residue→+*Residue := frobenius Residue 3

/-- The explicit skew-dual-number algebra: matrices [a b;0 a^3]. It models
the ramified quaternion maximal order modulo3. The identification with that
arithmetic order is separate; the finite ring here is actually constructed. -/
@[expose] def modelSubring : Subring (Matrix (Fin 2) (Fin 2) Residue) where
  carrier := {M | M 1 0=0 ∧ M 1 1=σ (M 0 0)}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro A B ⟨hA,hA'⟩ ⟨hB,hB'⟩
    constructor <;> simp [hA,hB,hA',hB',map_add]
  neg_mem' := by
    rintro A ⟨hA,hA'⟩
    constructor <;> simp [hA,hA',map_neg]
  mul_mem' := by
    rintro A B ⟨hA,hA'⟩ ⟨hB,hB'⟩
    constructor <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hA,hB,hA',hB',map_mul]

abbrev Model := modelSubring
noncomputable instance : Fintype Model := Fintype.ofFinite Model

@[expose] def pair (a b:Residue) : Model :=
  ⟨!![a,b;0,σ a],by simp [modelSubring]⟩

/-- Every model element has exactly two freely chosen residue coordinates. -/
@[expose] def coordinates : Model≃Residue×Residue where
  toFun M := (M.val 0 0,M.val 0 1)
  invFun ab := pair ab.1 ab.2
  left_inv M := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pair,M.property.1,M.property.2]
  right_inv ab := by simp [pair]

@[expose] def residue : Model→+*Residue where
  toFun M := M.val 0 0
  map_one' := by simp
  map_zero' := rfl
  map_add' A B := rfl
  map_mul' A B := by
    change (A.val*B.val) 0 0=A.val 0 0*B.val 0 0
    simp [Matrix.mul_apply,Fin.sum_univ_two,B.property.1]

theorem residue_surjective : Function.Surjective residue := by
  intro a
  exact ⟨pair a 0,rfl⟩

theorem ring_card : Nat.card Model=81 := by
  rw [Nat.card_congr coordinates,Nat.card_prod,residue_card]

/-- The genuine radical has square zero, proved by actual matrix multiplication. -/
theorem kernel_square (x:Model) (hx:residue x=0) : x^2=0 := by
  change x.val 0 0=0 at hx
  apply Subtype.ext
  change x.val^2=0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two,Matrix.mul_apply,Fin.sum_univ_two,x.property.1,x.property.2,hx]

theorem radical_card : Nat.card residue.toAddMonoidHom.ker=9 :=
  LevelThreeKernel318.kernel_card residue residue_surjective ring_card residue_card

theorem unit_card : Nat.card Modelˣ=72 :=
  LevelThreeKernel318.units_card residue residue_surjective kernel_square ring_card residue_card

theorem effective_card : Nat.card (Modelˣ ⧸ signs Model)=36 :=
  effective_kernel_card residue residue_surjective kernel_square ring_card residue_card
    (two_ne_zero_of_residue residue)

/-- The576 normalizer count for any actual extension by the literal W. -/
theorem normalizer_card {Γ:Type*} [Group Γ] (q:Γ→*W) (hq:Function.Surjective q)
    (e:q.ker≃*(Modelˣ ⧸ signs Model)) : Nat.card Γ=576 :=
  extension_card residue residue_surjective kernel_square ring_card residue_card
    (two_ne_zero_of_residue residue) q hq e

/-- Exact skew-dual-number multiplication, rather than only a cardinal model. -/
theorem pair_mul (a b c d:Residue) :
    pair a b*pair c d=pair (a*c) (a*d+b*σ c) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pair,Matrix.mul_apply,Fin.sum_univ_two,map_mul]

/-- The constructed noncommutative ring really is local. -/
instance : IsLocalRing Model where
  isUnit_or_isUnit_of_add_one {a b} hab := by
    by_cases ha:residue a=0
    · right
      apply (isUnit_iff_residue_ne_zero residue residue_surjective kernel_square b).mpr
      intro hb
      have h:=congrArg residue hab
      simp only [map_add,map_one,ha,hb,zero_add] at h
      exact zero_ne_one h
    · left
      exact (isUnit_iff_residue_ne_zero residue residue_surjective kernel_square a).mpr ha

/-- Transport the exact576 count to an actual local ring identified with the
explicit model. No ring/unit/kernel/normalizer cardinality is an input. -/
theorem normalizer_card_of_model {R Γ:Type*} [Ring R] [Fintype R] [Group Γ]
    (eR:R≃+*Model) (q:Γ→*W) (hq:Function.Surjective q)
    (e:q.ker≃*(Rˣ ⧸ signs R)) : Nat.card Γ=576 := by
  let π:R→+*Residue:=residue.comp eR.toRingHom
  have hs:Function.Surjective π:=residue_surjective.comp eR.surjective
  have hn:∀x:R,π x=0→x^2=0 := by
    intro x hx
    apply eR.injective
    rw [map_pow,map_zero]
    exact kernel_square (eR x) hx
  have hR:Nat.card R=81 := by rw [Nat.card_congr eR.toEquiv,ring_card]
  exact extension_card π hs hn hR residue_card (two_ne_zero_of_residue π) q hq e

/-- Final actual field-degree output from the local arithmetic model and the
regular fiber action, with the quaternion/model and extension bindings explicit. -/
theorem galois_degree_of_model {R Γ Ω:Type*} [Ring R] [Fintype R] [Group Γ]
    (eR:R≃+*Model) (q:Γ→*W) (hq:Function.Surjective q)
    (e:q.ker≃*(Rˣ ⧸ signs R))
    (L:Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (a:Γ→*Equiv.Perm Ω) (o:Ω) (ha:Function.Bijective (fun g:Γ=>a g o))
    (ρ:(L≃ₐ[ℚ]L)→*Equiv.Perm Ω)
    (hc:∀s:L≃ₐ[ℚ]L,∀g:Γ,∀x:Ω,ρ s (a g x)=a g (ρ s x))
    (hρ:Function.Injective ρ) :
    Module.finrank ℚ L∣576 ∧ Module.finrank ℚ L≤576 := by
  exact FiberCentralizer318.galois_torsor_degree_576 L a o ha
    (normalizer_card_of_model eR q hq e) ρ hc hρ

end RamifiedResidueModel318
