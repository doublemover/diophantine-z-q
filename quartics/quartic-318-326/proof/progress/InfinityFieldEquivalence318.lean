module
public import InfinityFieldMap318
public import FourRootGeneration318
public section
noncomputable section
namespace InfinityFieldEquivalence318
open Polynomial QuadraticPresentation318
open scoped TensorProduct
open InfinityFieldCoordinates318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev B:=TripleQuadraticField318.Raw (InfinityParameters318.parameter c)
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance infinityField : Field (B c):=(TripleQuadraticField318.infinity_field c).toField
@[expose] def phi : B c→+*L c := by
  letI:Algebra (RatFunc ℚ) (L c):=(coordinateField c).toRingHom.toAlgebra
  exact (InfinityFieldMap318.fieldHom c).toRingHom
@[expose] def image : Subfield (L c):=(phi c).fieldRange

@[expose] def generator : Fin 3→B c :=
  ![AdjoinRoot.root (polynomial (InfinityParameters318.parameter c 0))⊗ₜ[RatFunc ℚ]1,
    1⊗ₜ[RatFunc ℚ](AdjoinRoot.root (polynomial (InfinityParameters318.parameter c 1))⊗ₜ[RatFunc ℚ]1),
    1⊗ₜ[RatFunc ℚ](1⊗ₜ[RatFunc ℚ]AdjoinRoot.root (polynomial (InfinityParameters318.parameter c 2)))]

theorem phi_generator (j:Fin 3) : phi c (generator c j)=ratio c j := by
  fin_cases j <;> simp [phi,generator,InfinityFieldMap318.fieldHom,
    Algebra.TensorProduct.lift_tmul,InfinityFieldMap318.rootHom_root]

theorem coordinate_mem (f:RatFunc ℚ) : coordinateField c f∈image c :=
  ⟨algebraMap (RatFunc ℚ) (B c) f,InfinityFieldMap318.fieldHom_on_base c f⟩

theorem constant_mem (q:ℚ) : constant c q∈image c := by
  have h:=coordinate_mem c (algebraMap ℚ[X] (RatFunc ℚ) (C q))
  simpa only [InfinityFieldMap318.coordinateField_on_polynomial,Polynomial.aeval_C,constant] using h

theorem u_mem : u c∈image c := by
  have h:=coordinate_mem c (algebraMap ℚ[X] (RatFunc ℚ) X)
  simpa only [InfinityFieldMap318.coordinateField_on_polynomial,Polynomial.aeval_X] using h

theorem ratio_mem (j:Fin 3) : ratio c j∈image c := ⟨generator c j,phi_generator c j⟩

theorem t_mem : t c∈image c := by
  rw [recover_t]
  exact (image c).div_mem (constant_mem c _) ((image c).pow_mem (u_mem c) 2)

theorem root_mem (i:Fin 4) : root c i∈image c := by
  refine Fin.cases ?_ (fun j=>?_) i
  · rw [recover_root_zero]
    exact (image c).div_mem (constant_mem c _) (u_mem c)
  · rw [recover_root]
    exact (image c).mul_mem ((image c).div_mem (constant_mem c _) (u_mem c)) (ratio_mem c j)

theorem original_polynomial_mem (p:ℚ[X]) :
    algebraMap (RatFunc ℚ) (L c) (algebraMap ℚ[X] (RatFunc ℚ) p)∈image c := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using (image c).add_mem hp hq
  | monomial n a =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,RatFunc.algebraMap_C,
      RatFunc.algebraMap_X,map_mul,map_pow]
    apply (image c).mul_mem
    · have he:algebraMap (RatFunc ℚ) (L c) (RatFunc.C a)=constant c a := by
        rw [←RatFunc.algebraMap_eq_C,←IsScalarTower.algebraMap_apply ℚ (RatFunc ℚ) (L c)]
        rfl
      rw [he]
      exact constant_mem c a
    · exact (image c).pow_mem (t_mem c) n

theorem original_base_mem (f:RatFunc ℚ) : algebraMap (RatFunc ℚ) (L c) f∈image c := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    rw [map_div₀]
    exact (image c).div_mem (original_polynomial_mem c p) (original_polynomial_mem c q)

/-- Recovering t and every original root proves that the actual infinity
field map is onto the entire original contact field. -/
theorem phi_surjective : Function.Surjective (phi c) := by
  intro z
  let I:IntermediateField (RatFunc ℚ) (L c):=
    (image c).toIntermediateField (original_base_mem c)
  have htop:I.toSubalgebra=⊤ :=
    FourRootGeneration318.subalgebra_eq_top (SourceKummerField318.parameter c) I.toSubalgebra
      (root_mem c)
  have hz:z∈I.toSubalgebra := by rw [htop];trivial
  exact hz

/-- Actual function-field identification, with no surjectivity hypothesis. -/
@[expose] def fieldEquiv : B c≃+*L c :=
  RingEquiv.ofBijective (phi c) ⟨InfinityFieldMap318.fieldHom_injective c,phi_surjective c⟩

theorem fieldEquiv_on_coordinate (f:RatFunc ℚ) :
    fieldEquiv c (algebraMap (RatFunc ℚ) (B c) f)=coordinateField c f :=
  InfinityFieldMap318.fieldHom_on_base c f

theorem fieldEquiv_on_generator (j:Fin 3) :
    fieldEquiv c (generator c j)=ratio c j := phi_generator c j
end InfinityFieldEquivalence318
