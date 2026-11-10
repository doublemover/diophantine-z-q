module
public import PELOriginalMaximalQuotient318
public section
noncomputable section
namespace PELMaximalLocalOrbit318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318 PELOriginalBranchLabels318
open Filter Topology
set_option maxHeartbeats 1600000

/-- Near ANY point in an original labeled fixed locus, equality in the
FULL16 quotient is exactly the two-element stabilizer orbit. -/
theorem local_orbit_relation (i : Fin 5) (p : UnlevelledBase) (hp : p∈fixedLocus i) :
    ∃ U : Set UnlevelledBase,U∈𝓝 p ∧
      ∀ x∈U,∀ y∈U,
        PELOriginalMaximalQuotient318.projection x=PELOriginalMaximalQuotient318.projection y ↔
        x=y ∨ x=Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • y := by
  obtain ⟨U,hU,hstab⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Labels p
  refine ⟨U,hU,?_⟩
  intro x hx y hy
  rw [PELOriginalMaximalQuotient318.projection_eq_iff]
  constructor
  · rintro ⟨g,hg⟩
    have hgfix : g • p=p := hstab g ⟨x,⟨⟨y,hy,hg⟩,hx⟩⟩
    have hl := (locus_stabilizer_iff i p hp (Multiplicative.toAdd g)).mp hgfix
    rcases hl with hl | hl
    · have hg1 : g=1 := congrArg Multiplicative.ofAdd hl
      exact Or.inl (by simpa only [hg1,one_smul] using hg.symm)
    · have hgi : g=Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) :=
        congrArg Multiplicative.ofAdd hl
      exact Or.inr (by simpa only [hgi] using hg.symm)
  · rintro (rfl | h)
    · exact ⟨1,one_smul _ _⟩
    · exact ⟨Multiplicative.ofAdd (InertiaLabels318.fiveLabels i),h.symm⟩
end PELMaximalLocalOrbit318
