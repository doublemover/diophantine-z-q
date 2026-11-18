module
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.Tactic
public section
noncomputable section
namespace FiniteConjugateOrbitAlgebraic318
open Set MvPolynomial
variable {k Ω:Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

private def shift (ι:Type*) (a:k) : MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i+C a)) (aeval (fun i=>X i-C a))
    (by ext i <;> simp) (by ext i <;> simp)

/-- Independent translation in a transcendence basis extends to an
automorphism of the ambient algebraically closed field fixing the base.
Shifting all basis entries avoids any assumptions on the transcendence degree. -/
theorem translate {x:Ω} (hx:Transcendental k x) (a:k) :
    ∃σ:Ω≃ₐ[k]Ω, σ x=x+algebraMap k Ω a := by
  classical
  have hsingle : AlgebraicIndepOn k id ({x}:Set Ω) := by
    apply (algebraicIndependent_singleton_iff (⟨x,mem_singleton x⟩ : ({x}:Set Ω))).mpr
    exact hx
  obtain ⟨s,hsub,hs⟩ := exists_isTranscendenceBasis_superset hsingle
  let b : s → Ω := Subtype.val
  let z : s := ⟨x,hsub (mem_singleton x)⟩
  let A := Algebra.adjoin k (range b)
  letI : IsAlgClosure A Ω := IsAlgClosed.isAlgClosure_of_transcendence_basis b hs
  let e : A ≃ₐ[k] A := (hs.1.aevalEquiv.symm.trans (shift s a)).trans hs.1.aevalEquiv
  let g := IsAlgClosure.equivOfEquiv Ω Ω e.toRingEquiv
  let σ : Ω≃ₐ[k]Ω := { g with commutes' := by
    intro d
    change g (algebraMap k Ω d)=algebraMap k Ω d
    calc
      g (algebraMap k Ω d)=g (algebraMap A Ω (algebraMap k A d)) :=
        congrArg g (IsScalarTower.algebraMap_apply k A Ω d)
      _=algebraMap A Ω (e (algebraMap k A d)) := IsAlgClosure.equivOfEquiv_algebraMap _ _ _ _
      _=algebraMap k Ω d := (congrArg (algebraMap A Ω) (e.commutes d)).trans
        (IsScalarTower.algebraMap_apply k A Ω d).symm }
  refine ⟨σ,?_⟩
  have hx' : algebraMap A Ω (hs.1.aevalEquiv (X z))=x := by
    rw [hs.1.algebraMap_aevalEquiv];simp [z,b]
  change g x=_
  rw [←hx',IsAlgClosure.equivOfEquiv_algebraMap]
  change algebraMap A Ω (hs.1.aevalEquiv ((shift s a) (hs.1.aevalEquiv.symm (hs.1.aevalEquiv (X z)))))=_
  rw [AlgEquiv.symm_apply_apply]
  change algebraMap A Ω (hs.1.aevalEquiv (aeval (fun i:s=>X i+C a) (X z)))=_
  rw [aeval_X,hs.1.algebraMap_aevalEquiv,hs.1.algebraMap_aevalEquiv]
  simp

/-- A finite coordinate orbit under all field automorphisms implies genuine
algebraicity; no algebraicity hypothesis on the ambient extension. -/
theorem algebraic_of_finite [CharZero k] (x:Ω)
    (h:(range (fun σ:Ω≃ₐ[k]Ω => σ x)).Finite) : IsAlgebraic k x := by
  by_contra ht
  letI := h.fintype
  let f (n:ℕ) : range (fun σ:Ω≃ₐ[k]Ω=>σ x) :=
    ⟨x+algebraMap k Ω (n:k),translate ht (n:k)⟩
  have hi : Function.Injective f := by
    intro n m hh
    have h0 := congrArg Subtype.val hh
    change x+algebraMap k Ω (n:k)=x+algebraMap k Ω (m:k) at h0
    exact_mod_cast ((algebraMap k Ω).injective (add_left_cancel h0))
  exact (not_finite ℕ) (Finite.of_injective f hi)

end FiniteConjugateOrbitAlgebraic318
