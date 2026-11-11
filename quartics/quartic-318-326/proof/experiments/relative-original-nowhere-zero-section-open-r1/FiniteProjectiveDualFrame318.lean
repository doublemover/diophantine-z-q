module
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Flat.LocallyFree
public section
noncomputable section
namespace FiniteProjectiveDualFrame318
open scoped BigOperators
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The original finite-presentation/flat hypotheses imply projectivity by
actual maximal localizations, not by choosing a basis of the original module. -/
lemma projective_of_finitePresentation_flat [Module.FinitePresentation R M] [Module.Flat R M] :
    Module.Projective R M := by
  apply Module.projective_of_localization_maximal
  intro I hI
  letI := hI
  letI : Module.Free (Localization.AtPrime I) (LocalizedModule I.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  infer_instance

/-- A finite dual frame on the SAME module. The sum of the actual rank-one
operators is its identity; no global rank-one triviality is asserted. -/
structure Frame where
  n : ℕ
  out : Fin n → M →ₗ[R] R
  back : Fin n → R →ₗ[R] M
  total : ∑ i, (back i).comp (out i) = LinearMap.id

/-- A genuine finite free retract supplies a dual frame on the original
finite projective module. -/
lemma nonempty_frame [Module.Finite R M] [Module.Projective R M] : Nonempty (Frame R M) := by
  obtain ⟨n,f,g,hf,hg,hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let out (i : Fin n) : M →ₗ[R] R := (LinearMap.proj i).comp g
  let back (i : Fin n) : R →ₗ[R] M :=
    { toFun := fun r => f (Pi.single i r)
      map_add' := by
        intro a b
        have he : (Pi.single i (a+b) : Fin n → R) = Pi.single i a + Pi.single i b := by
          ext j
          by_cases h : j=i <;> simp_all [Pi.single_apply]
        rw [he,map_add]
      map_smul' := by
        intro a b
        have he : (Pi.single i (a • b) : Fin n → R) = a • Pi.single i b := by
          ext j
          by_cases h : j=i <;> simp_all [Pi.single_apply]
        rw [he,map_smul,RingHom.id_apply] }
  refine ⟨⟨n,out,back,?_⟩⟩
  ext m
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.id_apply]
  change (∑ i : Fin n, f (Pi.single i (g m i))) = m
  rw [← map_sum]
  have he : (∑ i : Fin n, Pi.single i (g m i)) = g m := by
    ext j
    simp [Pi.single_apply]
  rw [he]
  exact LinearMap.congr_fun hfg m
/-- Choose the actual finite retract frame after its nonempty construction. -/
def frame [Module.Finite R M] [Module.Projective R M] : Frame R M :=
  Classical.choice (nonempty_frame R M)
end FiniteProjectiveDualFrame318
