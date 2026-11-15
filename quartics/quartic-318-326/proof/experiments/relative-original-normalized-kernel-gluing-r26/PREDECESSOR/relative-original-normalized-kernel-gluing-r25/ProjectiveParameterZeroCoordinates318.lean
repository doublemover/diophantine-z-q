module
public import ProjectiveSectionParameter318
public section
noncomputable section
namespace ProjectiveParameterZeroCoordinates318
open scoped BigOperators TensorProduct
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "A" => ProjectiveSectionParameter318.algebra R P

@[expose] def coordinate (i : Fin F.size) : A := SymmetricAlgebra.ι R _ (F.coordinate i)

/-- A finite projective frame detects the actual represented section,
without choosing a free basis and over arbitrary coefficient rings. -/
lemma zero_iff (S : Type w) [CommRing S] [Algebra R S] (a : A →ₐ[R] S) :
    ProjectiveSectionParameter318.points R P S a=0 ↔ ∀ i,a (coordinate R P i)=0 := by
  constructor
  · intro hz i
    have h := ProjectiveSectionParameter318.coordinate R P S a (F.coordinate i)
    rw [hz,map_zero,LinearMap.zero_apply] at h
    exact h.symm
  · intro hz
    have h := FiniteProjectiveTensorDual318.reconstruct_pairing R P S F
      (ProjectiveSectionParameter318.points R P S a)
    rw [FiniteProjectiveTensorDual318.reconstruct] at h
    simp only [ProjectiveSectionParameter318.coordinate] at h
    have hs : (∑ i, a (coordinate R P i) ⊗ₜ[R] F.vector i)=0 := by
      simp only [hz,TensorProduct.zero_tmul,Finset.sum_const_zero]
    exact h.symm.trans hs

lemma nonzero_iff (S : Type w) [CommRing S] [Algebra R S] (a : A →ₐ[R] S) :
    ProjectiveSectionParameter318.points R P S a≠0 ↔ ∃ i,a (coordinate R P i)≠0 := by
  rw [zero_iff]
  exact not_forall

/-- The actual zero-parameter ideal, using the finite dual frame. Its
vanishing is a statement about the literal represented tensor section. -/
@[expose] def zeroIdeal : Ideal A := Ideal.span (Set.range (coordinate R P))

lemma zeroIdeal_le_kernel_iff (S : Type w) [CommRing S] [Algebra R S] (a : A →ₐ[R] S) :
    zeroIdeal R P ≤ RingHom.ker a.toRingHom ↔ ProjectiveSectionParameter318.points R P S a=0 := by
  rw [zero_iff]
  constructor
  · intro h i
    exact h (Ideal.subset_span ⟨i,rfl⟩)
  · intro h
    apply Ideal.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact h i
end ProjectiveParameterZeroCoordinates318
