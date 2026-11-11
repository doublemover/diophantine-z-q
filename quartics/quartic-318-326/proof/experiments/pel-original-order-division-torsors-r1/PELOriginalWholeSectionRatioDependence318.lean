module
public import PELOriginalFullSectionImageGrowth318
public import HomogeneousRatioBox318
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public section
noncomputable section
namespace PELOriginalWholeSectionRatioDependence318
open CubicBoxMonomials318 HomogeneousRatioBox318 PELOriginalGradedSectionRing318
open PELOriginalSectionMultiplication318 PELOriginalFullSectionImageGrowth318
variable (τ : ℂ) (hτ : 0 < τ.im)
section Family
variable {σ : Type*} (D : ℕ) (s : σ → homogeneous τ hτ D)
  (B : MvPolynomial σ ℂ) (A : Fin 3 → MvPolynomial σ ℂ)
  (hB : B.IsHomogeneous 1) (hA : ∀ i, (A i).IsHomogeneous 1)

@[expose] def boxImage (m : ℕ) :
    (Box m → ℂ) →ₗ[ℂ] degreePiece τ hτ D s (3*m) :=
  ((presentation τ hτ D s).toLinearMap.comp (cleared B A m)).codRestrict _
    (fun c => ⟨cleared B A m c, by simpa only [one_mul] using
      cleared_homogeneous B A m hB hA c, rfl⟩)

lemma boxImage_injective {K : Type*} [Field K] [Algebra ℂ K]
    (F : Ring τ hτ →ₐ[ℂ] K) (m : ℕ)
    (hden : F (presentation τ hτ D s B) ≠ 0)
    (hind : AlgebraicIndependent ℂ
      (fun i => F (presentation τ hτ D s (A i)) / F (presentation τ hτ D s B))) :
    Function.Injective (boxImage τ hτ D s B A hB hA m) := by
  intro c e h
  have hz : boxImage τ hτ D s B A hB hA m (c-e)=0 := by rw [map_sub,h,sub_self]
  have hf : F (presentation τ hτ D s (cleared B A m (c-e)))=0 := by
    have hh := congrArg (fun z : degreePiece τ hτ D s (3*m) => F z.val) hz
    change F (presentation τ hτ D s (cleared B A m (c-e)))=F 0 at hh
    simpa only [map_zero] using hh
  have hh := cleared_evaluation B A m (F.comp (presentation τ hτ D s)) hden (c-e)
  change F (presentation τ hτ D s (cleared B A m (c-e))) =
    (F (presentation τ hτ D s B))^(3*m) *
      MvPolynomial.aeval
        (fun i => F (presentation τ hτ D s (A i)) / F (presentation τ hτ D s B))
        (polynomial m (c-e)) at hh
  rw [hf] at hh
  have he := hind.eq_zero_of_aeval_eq_zero (polynomial m (c-e))
    ((mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hden))
  have hc : c-e=0 := (polynomial_injective m) (he.trans (map_zero (polynomial m)).symm)
  exact sub_eq_zero.mp hc

lemma family_not_independent {K : Type*} [Field K] [Algebra ℂ K]
    (F : Ring τ hτ →ₐ[ℂ] K) (hd : 0 < D)
    (hden : F (presentation τ hτ D s B) ≠ 0) :
    ¬ AlgebraicIndependent ℂ
      (fun i => F (presentation τ hτ D s (A i)) / F (presentation τ hτ D s B)) := by
  intro hind
  let m : ℕ := 9*D^2
  have hm : 0<m := Nat.mul_pos (by decide) (pow_pos hd _)
  have hdeg : D*(3*m)≠0 := Nat.mul_ne_zero (Nat.ne_of_gt hd)
    (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))
  have hdim : (m+1)^3 ≤ (D*(3*m))^2 := by
    calc
      (m+1)^3 = Module.finrank ℂ (Box m → ℂ) := by
        rw [Module.finrank_fintype_fun_eq_card,CubicBoxMonomials318.card]
      _ ≤ Module.finrank ℂ (degreePiece τ hτ D s (3*m)) :=
        LinearMap.finrank_le_finrank_of_injective
          (boxImage_injective τ hτ D s B A hB hA F m hden hind)
      _ ≤ (D*(3*m))^2 := by
        simpa only [if_neg hdeg] using whole_growth_bound τ hτ D s (3*m)
  have he : (D*(3*m))^2=m^3 := by dsimp [m]; ring
  rw [he] at hdim
  have hs : m^3<(m+1)^3 := by nlinarith [Nat.zero_le (m*m)]
  exact (not_lt_of_ge hdim) hs
end Family

/-- Three ratios of ANY genuine same-degree full original sections are
algebraically dependent. Numerators need not lie in the cubic coordinate
subalgebra, so this applies to genuinely new level-six sections. -/
theorem not_algebraicIndependent {K : Type*} [Field K] [Algebra ℂ K]
    (F : Ring τ hτ →ₐ[ℂ] K) (D : ℕ) (hd : 0 < D)
    (B : homogeneous τ hτ D) (A : Fin 3 → homogeneous τ hτ D)
    (hden : F (includeDegree τ hτ D B) ≠ 0) :
    ¬ AlgebraicIndependent ℂ
      (fun i => F (includeDegree τ hτ D (A i)) / F (includeDegree τ hτ D B)) := by
  let s : Option (Fin 3) → homogeneous τ hτ D := fun i => i.elim B A
  have h := family_not_independent τ hτ D s (MvPolynomial.X none)
    (fun i => MvPolynomial.X (some i))
    (MvPolynomial.isHomogeneous_X ℂ _) (fun i => MvPolynomial.isHomogeneous_X ℂ _) F hd
    (by simpa only [presentation,MvPolynomial.aeval_X,s,Option.elim_none] using hden)
  simpa only [presentation,MvPolynomial.aeval_X,s,Option.elim_none,Option.elim_some] using h

/-- Nonzero polynomial relation among those SAME literal full-section ratios. -/
theorem exists_relation {K : Type*} [Field K] [Algebra ℂ K]
    (F : Ring τ hτ →ₐ[ℂ] K) (D : ℕ) (hd : 0 < D)
    (B : homogeneous τ hτ D) (A : Fin 3 → homogeneous τ hτ D)
    (hden : F (includeDegree τ hτ D B) ≠ 0) :
    ∃ p : MvPolynomial (Fin 3) ℂ, p≠0 ∧
      MvPolynomial.aeval
        (fun i => F (includeDegree τ hτ D (A i)) / F (includeDegree τ hτ D B)) p=0 := by
  have h := not_algebraicIndependent τ hτ F D hd B A hden
  rw [algebraicIndependent_iff] at h
  push_neg at h
  obtain ⟨p,hp,hne⟩ := h
  exact ⟨p,hne,hp⟩
end PELOriginalWholeSectionRatioDependence318
