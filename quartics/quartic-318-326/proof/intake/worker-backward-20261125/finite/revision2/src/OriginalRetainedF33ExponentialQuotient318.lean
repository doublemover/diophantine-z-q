module
public import OriginalRetainedComplexPointsOverEEquiv318
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
noncomputable section

namespace OriginalRetainedF33ExponentialQuotient318
open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory MonoidalCategory
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedComplexPointFromE318
open OriginalRetainedComplexPointsOverEEquiv318
open scoped CategoryTheory.Obj CategoryTheory.MonObj Topology
attribute [local instance] Over.cartesianMonoidalCategory
abbrev Tangent := Fin 2→ℂ
abbrev IntegralLabels := Fin 4→ℤ

section Integral
variable {V:Type*} [AddCommGroup V]

/-- The four specified standard labels generate the whole original
integral coefficient group, not a rationally spanning subgroup. -/
theorem ext_of_four_cycles (f g:IntegralLabels→+V)
    (same:∀i:Fin 4,f (Pi.single i 1)=g (Pi.single i 1)) : f=g := by
  ext m
  have hs : (∑i:Fin 4,m i • Pi.single i (1:ℤ))=m := by
    simpa only [Pi.basisFun_repr,Pi.basisFun_apply] using
      ((Pi.basisFun ℤ (Fin 4)).sum_repr m)
  calc
    f m = f (∑i:Fin 4,m i • Pi.single i (1:ℤ)) := congrArg f hs.symm
    _ = ∑i:Fin 4,m i • f (Pi.single i 1) := by simp only [map_sum,map_zsmul]
    _ = ∑i:Fin 4,m i • g (Pi.single i 1) := by simp only [same]
    _ = g (∑i:Fin 4,m i • Pi.single i (1:ℤ)) := by simp only [map_sum,map_zsmul]
    _ = g m := congrArg g hs
end Integral

variable {A₃₃ Y₃₃:Scheme} (a₃₃:A₃₃⟶Y₃₃) [GrpObj (Over.mk a₃₃)]
  {E:Type} [Field E] (σ:E→+*ℂ) (P:Spec (CommRingCat.of E)⟶Y₃₃)
local notation "T" => Spec (CommRingCat.of ℂ)
local notation "F" => fiber a₃₃ (specOf σ≫P)
abbrev Points := Over.mk (𝟙 T)⟶F

/-- The literal point group of the original group object. The product
is the existing Cartesian.Monoid product; inversion is composition
with its actual inverse arrow, not an independently supplied group. -/
instance actualPointGroup : Group (Points a₃₃ σ P) where
  inv f := f≫(GrpObj.inv (X:=F))
  inv_mul_cancel f := calc
    lift (f≫(GrpObj.inv (X:=F))) f≫(MonObj.mul (X:=F))
    _ = (f≫lift (GrpObj.inv (X:=F)) (𝟙 F))≫(MonObj.mul (X:=F)) := by simp
    _ = toUnit (Over.mk (𝟙 T))≫(MonObj.one (X:=F)) := by rw [Category.assoc]; simp

local notation "M" => Points a₃₃ σ P
variable (exp:Tangent→+Additive M)
  (periods:IntegralLabels→+Tangent)
  (frame:IntegralLabels≃+exp.ker)
  (four_labels:∀i:Fin 4,(frame (Pi.single i 1):Tangent)=periods (Pi.single i 1))

include four_labels in
theorem every_label (m:IntegralLabels):
    (frame m:Tangent)=periods m := by
  let read : IntegralLabels→+Tangent := exp.ker.subtype.comp frame.toAddMonoidHom
  have eq : read=periods := ext_of_four_cycles read periods four_labels
  exact DFunLike.congr_fun eq m

include four_labels in
/-- The actual analytic kernel equals the full original period lattice.
Only values at the four labelled basis cycles were needed. -/
theorem exact_analytic_kernel :
    periods.range=exp.ker := by
  ext z
  constructor
  · rintro ⟨m,rfl⟩
    rw [←every_label a₃₃ σ P exp periods frame four_labels m]
    exact (frame m).property
  · intro hz
    obtain ⟨m,hm⟩:=frame.surjective ⟨z,hz⟩
    exact ⟨m,(every_label a₃₃ σ P exp periods frame four_labels m).symm.trans
      (congrArg Subtype.val hm)⟩

section Connected
variable [TopologicalSpace (Additive M)] [PreconnectedSpace (Additive M)]
  [SeparatelyContinuousAdd (Additive M)]

/-- A true local exponential on the connected analytic point group is
surjective on the whole group. No unit property of the algebraic
Gamma coframe or of its derivative is required for this argument. -/
theorem actual_exp_surjective
    (near:(exp.range : Set (Additive M))∈𝓝 (0:Additive M)) :
    Function.Surjective exp := by
  have isOpenRange:=AddSubgroup.isOpen_of_mem_nhds exp.range near
  have isClosedRange:=AddSubgroup.isClosed_of_isOpen exp.range isOpenRange
  have all : (exp.range : Set (Additive M))=Set.univ :=
    (show IsClopen (exp.range : Set (Additive M)) from ⟨isClosedRange,isOpenRange⟩).eq_univ
      ⟨0,exp.range.zero_mem⟩
  intro y
  have hm:y∈(exp.range : Set (Additive M)):=all.symm ▸ Set.mem_univ y
  exact hm
end Connected

variable (onto:Function.Surjective exp)

include four_labels onto in
/-- The quotient equivalence is induced by the ONE actual exponential.
It is no longer an extra supplied group isomorphism. -/
def inducedOnQuotient : (Tangent ⧸ periods.range)≃+Additive M :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (exact_analytic_kernel a₃₃ σ P exp periods frame four_labels)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective exp onto)

include four_labels onto in
theorem induced_reads_exp (z:Tangent):
    inducedOnQuotient a₃₃ σ P exp periods frame four_labels onto
      (QuotientAddGroup.mk' periods.range z)=exp z := by
  change QuotientAddGroup.quotientKerEquivOfSurjective exp onto
    (QuotientAddGroup.quotientAddEquivOfEq
      (exact_analytic_kernel a₃₃ σ P exp periods frame four_labels)
      (QuotientAddGroup.mk z))=exp z
  exact congrArg (QuotientAddGroup.quotientKerEquivOfSurjective exp onto)
    (QuotientAddGroup.quotientAddEquivOfEq_mk
      (exact_analytic_kernel a₃₃ σ P exp periods frame four_labels) z)

include four_labels onto in
def actualGroupUniformization : Multiplicative (Tangent ⧸ periods.range)≃*M :=
  AddEquiv.toMultiplicativeLeft (inducedOnQuotient a₃₃ σ P exp periods frame four_labels onto)

include four_labels onto in
theorem actualGroupUniformization_reads_exp (z:Tangent):
    actualGroupUniformization a₃₃ σ P exp periods frame four_labels onto
      (Multiplicative.ofAdd (QuotientAddGroup.mk' periods.range z))=(exp z).toMul :=
  congrArg Additive.toMul (induced_reads_exp a₃₃ σ P exp periods frame four_labels onto z)

end OriginalRetainedF33ExponentialQuotient318
