module
public import FinitePivotChartPoint318
public import SeparatedContactPivot318
public import OriginalFinitePivotCanonicalExtension318
public section
noncomputable section
namespace OriginalEvenFiniteCanonicalCenter318
open NumberField Polynomial AlgebraicGeometry CategoryTheory FourRootPivot318
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 FinitePivotCanonicalSource318
variable (c : Fin 4 → ℚˣ) (tau : ℚ) (w : FinitePlace (K c tau)) (D : Data c tau w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c tau w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "d" => D.coefficients
structure Center (i : Fin 4) where
  coordinate : V
  otherRoots : Fin 3 → V
  root_equation : ∀ j,(otherRoots j)^2=Polynomial.eval coordinate
    (OddTwistDilatationCoordinates318.coefficient 1 (D.unit i) (a i) (others V d i) (others V a i) j)
  root_unit : ∀ j,IsUnit (otherRoots j)
  contact : algebraMap V (K c tau) (Polynomial.eval coordinate
    (OddTwistDilatationCoordinates318.contact 1 (D.unit i) (a i)))=(tau:K c tau)
  original_pivot : algebraMap V (K c tau) coordinate=D.normalizedRoots i
  original_other : ∀ j,algebraMap V (K c tau) (otherRoots j)=D.normalizedRoots (indices i j.succ)
variable (he : ∀ k,D.exponent k=0)
include he in
lemma coefficient_even (i : Fin 4) : d i=(D.unit i:V)*1 := by simp [Data.coefficients,he i]
include he in
/-- The original all-even finite point produces its own pivot and actual
unit roots. No chosen good pivot or nonvanishing differential is assumed. -/
theorem exists_center (ht : w (tau:K c tau)≤1)
    (hsep : ∀ i j : Fin 4,i≠j→IsUnit (a i-a j)) :
    ∃ i,Nonempty (Center c tau w D i) := by
  obtain ⟨T,r,hT,hr,hrel⟩ := OriginalAllPlaceRootBounds318.finite_coordinates c tau w D ht
  obtain ⟨i,hi⟩ := SeparatedContactPivot318.exists_pivot a T hsep
  have hdi : d i=(D.unit i:V) := by simpa only [mul_one] using coefficient_even c tau w D he i
  have hcoord : T=a i+(↑(D.unit i)⁻¹:V)*(r i)^2 := by
    rw [hrel i,hdi,←mul_assoc,Units.inv_mul,one_mul]
    ring
  have hvalue : Polynomial.eval (r i) (OddTwistDilatationCoordinates318.contact 1 (D.unit i) (a i))=T := by
    simpa only [OddTwistDilatationCoordinates318.contact,eval_add,eval_C,eval_mul,eval_pow,eval_X,one_mul]
      using hcoord.symm
  have hroot (j : Fin 3) : (r (indices i j.succ))^2=Polynomial.eval (r i)
      (OddTwistDilatationCoordinates318.coefficient 1 (D.unit i) (a i) (others V d i) (others V a i) j) := by
    simp only [OddTwistDilatationCoordinates318.coefficient,eval_mul,eval_C,eval_sub,hvalue]
    exact hrel (indices i j.succ)
  have hu (j : Fin 3) : IsUnit (r (indices i j.succ)) := by
    have hj : indices i j.succ≠i := by
      intro h
      exact Fin.succ_ne_zero j ((indices_injective i) (h.trans (indices_zero i).symm))
    apply (isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp
    rw [hrel (indices i j.succ),coefficient_even c tau w D he,mul_one]
    exact (D.unit (indices i j.succ)).isUnit.mul (hi _ hj)
  refine ⟨i,⟨⟨r i,fun j => r (indices i j.succ),hroot,hu,?_,hr i,?_⟩⟩⟩
  · rw [hvalue,hT]
  · exact fun j => hr (indices i j.succ)

variable (i : Fin 4) (P : Center c tau w D i)
local notation "C" => FinitePivotCanonicalSource318.Chart V 1 (D.unit i) d a i
@[expose] def modelPoint : DVRNormalizedFiniteOrder318.Order V d a →+* V :=
  FinitePivotChartPoint318.modelPoint V 1 (D.unit i) d a i (coefficient_even c tau w D he i)
    P.coordinate P.otherRoots P.root_equation P.root_unit
lemma modelPoint_roots (k : Fin 4) : algebraMap V (K c tau) (modelPoint c tau w D he i P
    (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient V d a) k))=
      D.normalizedRoots k := by
  obtain ⟨j,rfl⟩ := (indexEquiv i).surjective k
  change algebraMap V (K c tau) (modelPoint c tau w D he i P
    (FourRootOrderSigns318.generator _ (indices i j)))=_
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [indices_zero,modelPoint,FinitePivotChartPoint318.modelPoint_pivot,one_mul]
    exact P.original_pivot
  · rw [modelPoint,FinitePivotChartPoint318.modelPoint_other]
    exact P.original_other j

theorem generic_extension : Spec.map (CommRingCat.ofHom (algebraMap V (K c tau))) ≫
    (Spec.map (CommRingCat.ofHom (modelPoint c tau w D he i P)) ≫
      NormalizedWholeOpenMaps318.finiteChart V d a)=D.genericPoint :=
  NormalizedGenericPointExtension318.finite_extension V (K c tau) d a (tau:K c tau)
    D.normalizedRoots D.root_equation
    (Polynomial.eval P.coordinate (OddTwistDilatationCoordinates318.contact 1 (D.unit i) (a i)))
    P.contact (modelPoint c tau w D he i P)
    (FinitePivotChartPoint318.modelPoint_polynomial V 1 (D.unit i) d a i (coefficient_even c tau w D he i)
      P.coordinate P.otherRoots P.root_equation P.root_unit)
    (modelPoint_roots c tau w D he i P)
end OriginalEvenFiniteCanonicalCenter318
