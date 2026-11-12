module
public import IntegralNormalDifferentialDuality318
public section
noncomputable section
namespace IntegralNormalTraceForms318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "B" => OpenOrder R a d
local notation "F" => Base R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=F) N
local notation "e" => IntegralNormalSourceDifferentialFrame318.frame R a d

/-- The ENTIRE trace-codifferent is embedded in actual source
Kaehler differentials using the normalized original dT, N-semi-linearly
for the literal inclusion N -> B. No freeness of L is asserted. -/
@[expose] def form : L →ₛₗ[algebraMap N B] KaehlerDifferential R B where
  toFun z := e.symm z.val
  map_add' z q := e.symm.map_add z.val q.val
  map_smul' n z := by
    change e.symm (n.val*z.val)=n.val • e.symm z.val
    exact e.symm.map_smul n.val z.val

@[simp] theorem coefficient (z : L) : e (form R a d z)=z.val :=
  e.apply_symm_apply z.val

theorem injective : Function.Injective (form R a d) := by
  intro z q h
  apply Subtype.ext
  simpa only [coefficient] using congrArg e h

/-- Full image criterion, not just a statement about a chosen section. -/
theorem range_iff (ω : KaehlerDifferential R B) :
    ω ∈ Set.range (form R a d) ↔ e ω ∈ L := by
  constructor
  · rintro ⟨z,rfl⟩
    rw [coefficient]
    exact z.property
  · intro h
    refine ⟨⟨e ω,h⟩,?_⟩
    exact e.symm_apply_apply ω

theorem literal_dt (z : L) : form R a d z=z.val •
    KaehlerDifferential.D R B (IntegralNormalSourceDifferentialFrame318.coordinate R a d) := by
  apply e.injective
  rw [coefficient,map_smul,IntegralNormalSourceDifferentialFrame318.frame_D,
    smul_eq_mul,mul_one]
end IntegralNormalTraceForms318
