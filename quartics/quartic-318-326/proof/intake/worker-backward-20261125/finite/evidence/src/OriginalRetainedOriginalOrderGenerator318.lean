module
public import OriginalLiteralMarkedRealPeriodColumns318
public import OriginalRetainedF33ExponentialQuotient318

@[expose] public section
noncomputable section

namespace OriginalRetainedOriginalOrderGenerator318
open AlgebraicGeometry CategoryTheory
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedF33ExponentialQuotient318
open OriginalLiteralMarkedRealPeriodColumns318
open scoped Matrix CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable (α β:ℝ) (τ:ℂ)
def normalizedGenerator : Tangent := ![τ,1]

/-- The original four quaternion order actions on the normalized
Lie coordinates, in the frozen order [1,i,(1+j)/2,i/2+k/10]. -/
def labelMatrix (k:Fin 4):Matrix (Fin 2) (Fin 2) ℝ :=
  matrixRead ((orderMatrix α β).mulVec (Pi.single k 1))

def labelLieAction (k:Fin 4):Tangent→ₗ[ℝ]Tangent :=
  (Matrix.toLin' ((labelMatrix α β k).map fun x:ℝ=>(x:ℂ))).restrictScalars ℝ

theorem label_generator_exact (k:Fin 4):
    labelLieAction α β k (normalizedGenerator τ)=
      evaluation τ (matrixRead ((orderMatrix α β).mulVec (Pi.single k 1))) := by
  funext i
  change (((labelMatrix α β k).map fun x:ℝ=>(x:ℂ)).mulVec (normalizedGenerator τ)) i=_
  simp [normalizedGenerator,labelMatrix,evaluation,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

def integralOrderWord : IntegralLabels→+Tangent where
  toFun n := ∑i:Fin 4,n i • labelLieAction α β i (normalizedGenerator τ)
  map_zero' := by simp
  map_add' m n := by simp only [Pi.add_apply,add_zsmul,Finset.sum_add_distrib]

theorem word_single (i:Fin 4):
    integralOrderWord α β τ (Pi.single i 1)=labelLieAction α β i (normalizedGenerator τ) := by
  change (∑j:Fin 4,(Pi.single i (1:ℤ)) j • labelLieAction α β j (normalizedGenerator τ))=_
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same,one_zsmul]
  · intro j hj ne
    rw [Pi.single_eq_of_ne ne,zero_zsmul]
  · intro no
    exact (no (Finset.mem_univ i)).elim

variable (ha:α^2=210) (hb:β^2=5) (hy:0<τ.im)

/-- The literal action of the original order on its one normalized
generator produces the already computed columns, with no new labels. -/
theorem whole_word_eq_columns :
    integralOrderWord α β τ=integerPeriods α β ha hb τ hy := by
  apply ext_of_four_cycles
  intro i
  rw [word_single,label_generator_exact]
  have hcast : (fun j:Fin 4=>(((Pi.single i (1:ℤ)) j:ℤ):ℝ))=Pi.single i 1 := by
    funext j
    by_cases ij:j=i
    · subst j
      simp
    · simp only [Pi.single_eq_of_ne ij,Int.cast_zero]
  change _=actualColumns α β ha hb τ hy (fun j=>(((Pi.single i (1:ℤ)) j:ℤ):ℝ))
  rw [hcast,columns_are_actual_evaluation]

theorem word_injective : Function.Injective (integralOrderWord α β τ) := by
  intro m n h
  rw [whole_word_eq_columns α β τ ha hb hy] at h
  have eq := (actualColumns α β ha hb τ hy).injective h
  funext j
  exact Int.cast_injective (congrFun eq j)

variable {A₃₃ Y₃₃:Scheme} (a₃₃:A₃₃⟶Y₃₃) [GrpObj (Over.mk a₃₃)]
  {E:Type} [Field E] (σ:E→+*ℂ) (P:Spec (CommRingCat.of E)⟶Y₃₃)
local notation "M" => Additive (Points a₃₃ σ P)
variable (exp:Tangent→+M)
  (onPts:Fin 4→(M→+M))
  (period:exp (normalizedGenerator τ)=0)
  (natural:∀i z,exp (labelLieAction α β i z)=onPts i (exp z))

include period natural in
theorem every_word_in_actual_kernel (n:IntegralLabels):
    integralOrderWord α β τ n∈exp.ker := by
  change exp (∑i:Fin 4,n i • labelLieAction α β i (normalizedGenerator τ))=0
  simp only [map_sum,map_zsmul,natural,period,map_zero,zsmul_zero,Finset.sum_const_zero]

include period natural in
def wordInKernel : IntegralLabels→+exp.ker where
  toFun n:=⟨integralOrderWord α β τ n,
    every_word_in_actual_kernel α β τ a₃₃ σ P exp onPts period natural n⟩
  map_zero' := Subtype.ext (map_zero (integralOrderWord α β τ))
  map_add' m n := Subtype.ext (map_add (integralOrderWord α β τ) m n)

include period natural in
/-- Only integral principality remains: the original kernel is generated
by the original order acting on the actual normalized generator. The
frame and its four labelled readings are outputs. -/
def frameFromActualGenerator
    (generate:∀z:exp.ker,∃n:IntegralLabels,integralOrderWord α β τ n=z.val):
    IntegralLabels≃+exp.ker := by
  let q := wordInKernel α β τ a₃₃ σ P exp onPts period natural
  apply AddEquiv.ofBijective q
  constructor
  · intro x y h
    exact word_injective α β τ ha hb hy (congrArg Subtype.val h)
  · intro z
    obtain ⟨n,hn⟩:=generate z
    exact ⟨n,Subtype.ext hn⟩

include period natural in
theorem frameFromActualGenerator_label
    (generate:∀z:exp.ker,∃n:IntegralLabels,integralOrderWord α β τ n=z.val) (i:Fin 4):
    (frameFromActualGenerator α β τ ha hb hy a₃₃ σ P exp onPts period natural generate
      (Pi.single i 1)).val=integerPeriods α β ha hb τ hy (Pi.single i 1) :=
  DFunLike.congr_fun (whole_word_eq_columns α β τ ha hb hy) (Pi.single i 1)

end OriginalRetainedOriginalOrderGenerator318
