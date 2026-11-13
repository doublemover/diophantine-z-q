module
public import ActualTwoDescentOriginalPrincipalInverseCertificateRebuild318
public section
noncomputable section
namespace ActualTwoDescentFractionalGeneratorModuleRebuild318
variable (R F : Type*) [CommRing R] [Field F] [Algebra R F]

def coefficientMap (g : F) : R →ₗ[R] F where
  toFun r := algebraMap R F r*g
  map_add' r s := by rw [map_add,add_mul]
  map_smul' r s := by
    change algebraMap R F (r*s)*g=algebraMap R F r*(algebraMap R F s*g)
    rw [map_mul,mul_assoc]

def lattice (g : F) : Submodule R F := (coefficientMap R F g).range

lemma mem_lattice (g z : F) : z ∈ lattice R F g ↔
    ∃ r : R,algebraMap R F r*g=z := Iff.rfl

/-- Full image, with the original scalar embedding retained. -/
def frame (g : F) (hg : g ≠ 0) (hi : Function.Injective (algebraMap R F)) :
    R ≃ₗ[R] lattice R F g :=
  LinearEquiv.ofBijective (coefficientMap R F g).rangeRestrict (by
    constructor
    · intro r s h
      exact hi (mul_right_cancel₀ hg (congrArg Subtype.val h))
    · intro z
      obtain ⟨r,hr⟩ := z.property
      exact ⟨r,Subtype.ext hr⟩)

lemma frame_value (g : F) (hg : g ≠ 0) (hi : Function.Injective (algebraMap R F))
    (r : R) : (frame R F g hg hi r : F)=algebraMap R F r*g := rfl
end ActualTwoDescentFractionalGeneratorModuleRebuild318
