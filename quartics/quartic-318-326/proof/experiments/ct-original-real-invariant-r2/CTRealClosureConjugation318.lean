module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
import all Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Tactic.NormNum
public section
noncomputable section

namespace CTRealClosureConjugation318

abbrev RealGal := Field.absoluteGaloisGroup ℝ
abbrev Rbar := AlgebraicClosure ℝ

/-- An ℝ-algebra equivalence only; the actual Gal topology remains Krull. -/
def realClosureEquiv : Rbar ≃ₐ[ℝ] ℂ :=
  letI : IsAlgClosure ℝ ℂ := ⟨inferInstance, Algebra.IsAlgebraic.of_finite ℝ ℂ⟩
  IsAlgClosure.equiv ℝ Rbar ℂ

def realAutTransport : RealGal ≃* (ℂ ≃ₐ[ℝ] ℂ) :=
  show (Rbar ≃ₐ[ℝ] Rbar) ≃* (ℂ ≃ₐ[ℝ] ℂ) from realClosureEquiv.autCongr

def realConjugation : RealGal := realAutTransport.symm Complex.conjAe

theorem realAutTransport_conjugation : realAutTransport realConjugation = Complex.conjAe :=
  realAutTransport.apply_symm_apply _

theorem realAutTransport_apply (g : RealGal) (x : Rbar) :
    realAutTransport g (realClosureEquiv x) =
      realClosureEquiv ((show Rbar ≃ₐ[ℝ] Rbar from g) x) := by
  change realClosureEquiv ((show Rbar ≃ₐ[ℝ] Rbar from g)
    (realClosureEquiv.symm (realClosureEquiv x))) = _
  rw [realClosureEquiv.symm_apply_apply]

theorem realGal_cases (g : RealGal) : g=1 ∨ g=realConjugation := by
  rcases Complex.real_algHom_eq_id_or_conj (realAutTransport g).toAlgHom with h | h
  · left
    apply realAutTransport.injective
    rw [map_one]
    apply AlgEquiv.ext
    intro z
    change ((realAutTransport g).toAlgHom) z = AlgHom.id ℝ ℂ z
    rw [h]
  · right
    apply realAutTransport.injective
    rw [realAutTransport_conjugation]
    apply AlgEquiv.ext
    intro z
    change ((realAutTransport g).toAlgHom) z = Complex.conjAe.toAlgHom z
    rw [h]

theorem realConjugation_square : realConjugation*realConjugation=1 := by
  apply realAutTransport.injective
  rw [map_mul,map_one,realAutTransport_conjugation]
  apply AlgEquiv.ext
  intro z
  change (starRingEnd ℂ) ((starRingEnd ℂ) z)=z
  exact star_star z

theorem complexConj_I_ne_I : (starRingEnd ℂ) Complex.I ≠ Complex.I := by
  intro h
  have h' := congrArg Complex.im h
  norm_num [Complex.conj_I] at h'

theorem realConjugation_ne_one : realConjugation≠1 := by
  intro h
  have hA := congrArg realAutTransport h
  rw [realAutTransport_conjugation,map_one] at hA
  exact complexConj_I_ne_I (congrArg (fun a : ℂ ≃ₐ[ℝ] ℂ => a Complex.I) hA)

/-- The topology statement is on the exact absolute group, proved by the
open stabilizer of the preimage of I rather than changing topology. -/
theorem realGal_discrete : DiscreteTopology RealGal := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  let x := realClosureEquiv.symm Complex.I
  let H : Subgroup (Rbar ≃ₐ[ℝ] Rbar) := MulAction.stabilizer (Rbar ≃ₐ[ℝ] Rbar) x
  let S : Set RealGal := (H : Set (Rbar ≃ₐ[ℝ] Rbar))
  have hO : IsOpen S := by
    change IsOpen (H : Set (Rbar ≃ₐ[ℝ] Rbar))
    exact stabilizer_isOpen_of_isIntegral x
  have he : S=({1} : Set RealGal) := by
    ext g
    rcases realGal_cases g with rfl | rfl
    · exact ⟨fun _ => Set.mem_singleton _,
        fun _ => by change (1 : Rbar ≃ₐ[ℝ] Rbar) ∈ H; exact H.one_mem⟩
    · constructor
      · intro h
        have hx : (show Rbar ≃ₐ[ℝ] Rbar from realConjugation) x = x := h
        have hI := (realAutTransport_apply realConjugation x).trans (congrArg realClosureEquiv hx)
        dsimp only [x] at hI
        rw [realClosureEquiv.apply_symm_apply,realAutTransport_conjugation] at hI
        exact (complexConj_I_ne_I hI).elim
      · intro h
        exact (realConjugation_ne_one (Set.mem_singleton_iff.mp h)).elim
  rwa [he] at hO

end CTRealClosureConjugation318
