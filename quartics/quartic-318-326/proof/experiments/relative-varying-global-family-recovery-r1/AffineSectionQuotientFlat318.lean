module
public import ProjectiveFiberwiseCokernelFlat318
public import FiniteProjectiveDualRetract318
public import ProjectiveCoefficientRestriction318
public import ProjectiveSectionIdeal318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace AffineSectionQuotientFlat318
universe u
variable (R S P : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup P] [Module S P]

/-- The actual section-evaluation map, viewed over the parameter ring. -/
@[expose] def evaluation (s : P) : Module.Dual S P →ₗ[R] S :=
  (ProjectiveSectionIdeal318.evaluation S P s).restrictScalars R

@[expose] def quotient (s : P) : S →ₗ[R] S ⧸ ProjectiveSectionIdeal318.ideal S P s :=
  (Ideal.Quotient.mkₐ R (ProjectiveSectionIdeal318.ideal S P s)).toLinearMap

lemma exact (s : P) : Function.Exact (evaluation R S P s) (quotient R S P s) := by
  rw [LinearMap.exact_iff]
  ext a
  change Ideal.Quotient.mk (ProjectiveSectionIdeal318.ideal S P s) a=0 ↔
    ∃ φ : Module.Dual S P, φ s=a
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Flatness of the LITERAL section-zero quotient over the parameter
ring. A finite dual-frame retract constructs coefficient projectivity of
the actual evaluation source; the original section ideal supplies exactness.
Only residue injectivity of this precise evaluation map remains as input. -/
lemma flat (s : P) [Module.Free R S] [Module.Finite S P] [Module.Projective S P]
    (hf : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective ((evaluation R S P s).baseChange (R ⧸ m))) :
    Module.Flat R (S ⧸ ProjectiveSectionIdeal318.ideal S P s) := by
  let F := FiniteProjectiveEvaluationFrame318.frame S P
  letI := (FiniteProjectiveDualRetract318.properties S P F).1
  letI := (FiniteProjectiveDualRetract318.properties S P F).2
  letI : Module.Projective R (Module.Dual S P) :=
    ProjectiveCoefficientRestriction318.projective R S (Module.Dual S P)
  exact ProjectiveFiberwiseCokernelFlat318.flat (evaluation R S P s) (quotient R S P s)
    (exact R S P s) (Ideal.Quotient.mkₐ_surjective R _) hf
end AffineSectionQuotientFlat318
