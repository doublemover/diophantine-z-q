module
public import PELNormalizerProjectiveLevel318
public section
noncomputable section
namespace PELGlobalIntegralUnitLifts318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELOrderReductionThree318
set_option maxHeartbeats 1400000

@[expose] def generatorCoefficients : Fin 3 → Coordinates :=
  ![![0,0,1,0],![-44,10,15,-15],![-29,25,-15,-35]]
@[expose] def inverseCoefficients : Fin 3 → Coordinates :=
  ![![-1,0,1,0],![-29,-10,-15,15],![-44,-25,15,35]]

/-- Three actual GLOBAL units in the original integral quaternion order. -/
@[expose] def generator (j : Fin 3) : orderˣ where
  val := coordinatesEquiv (generatorCoefficients j)
  inv := coordinatesEquiv (inverseCoefficients j)
  val_inv := by
    apply Subtype.ext
    change embed (generatorCoefficients j)*embed (inverseCoefficients j)=1
    fin_cases j <;> ext <;> norm_num [generatorCoefficients,inverseCoefficients,embed]
  inv_val := by
    apply Subtype.ext
    change embed (inverseCoefficients j)*embed (generatorCoefficients j)=1
    fin_cases j <;> ext <;> norm_num [generatorCoefficients,inverseCoefficients,embed]

theorem generator_norm (j : Fin 3) :
    reducedNorm ((generator j:order):B)=if j=0 then -1 else 1 := by
  change reducedNorm (embed (generatorCoefficients j))=_
  fin_cases j <;> norm_num [generatorCoefficients,embed,reducedNorm]

@[expose] def finiteGenerator : Fin 3 → Reduction :=
  ![⟨2,0,2,0⟩,⟨1,1,0,0⟩,⟨1,0,0,1⟩]

theorem generator_reduction (j : Fin 3) :
    reduction (generator j:order)=finiteGenerator j := by
  change reduction (coordinatesEquiv (generatorCoefficients j))=_
  rw [reduction_coordinates]
  fin_cases j <;> ext <;> norm_num [generatorCoefficients,reduceCoordinates,finiteGenerator]

@[expose] def globalWord (k : Fin 8) (a b : Fin 3) : orderˣ :=
  generator 0^k.val*generator 1^a.val*generator 2^b.val
@[expose] def finiteWord (k : Fin 8) (a b : Fin 3) : Reduction :=
  finiteGenerator 0^k.val*finiteGenerator 1^a.val*finiteGenerator 2^b.val

theorem word_reduction (k : Fin 8) (a b : Fin 3) :
    reduction (globalWord k a b:order)=finiteWord k a b := by
  simp only [globalWord,finiteWord,Units.val_mul,Units.val_pow,map_mul,map_pow,generator_reduction]

/-- All72 finite units have explicit original integral unit lifts. The
norm−1 generator is retained; this is NOT norm-one-unit surjectivity onto72. -/
theorem finite_cover (x : Reduction) (hx : PELReductionResidueField318.residue x≠0) :
    ∃ k : Fin 8,∃ a b : Fin 3,finiteWord k a b=x := by
  obtain ⟨r,u,j,v⟩ := x
  fin_cases r <;> fin_cases u <;> fin_cases j <;> fin_cases v
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exact ⟨6,0,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨6,2,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨6,1,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,0,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,1,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,2,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exact ⟨6,0,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨6,2,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨6,1,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,0,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,1,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,2,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exfalso
    apply hx
    ext <;> norm_num [PELReductionResidueField318.residue]
  · exact ⟨6,0,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨6,2,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨6,1,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,0,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,1,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨2,2,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,0,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,0,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,0,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,0,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,1,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,2,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,0,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,2,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,1,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,1,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,1,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,1,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,2,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,0,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,1,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,2,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,1,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,0,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,2,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,2,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨0,2,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,1,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,2,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨5,0,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,1,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,0,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨7,2,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,0,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,0,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,0,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,0,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,1,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,2,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,0,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,2,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,1,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,2,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,2,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,2,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,1,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,2,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,0,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,1,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,0,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,2,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,1,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,1,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨4,1,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,2,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,0,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨3,1,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,2,2,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,1,0,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
  · exact ⟨1,0,1,by ext <;> norm_num [finiteWord,finiteGenerator,pow_succ,pow_two]⟩
end PELGlobalIntegralUnitLifts318
