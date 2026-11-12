module
public import ProjectiveParameterUnitSlice318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace ProjectiveParameterSliceAlgebra318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
variable (i : Fin F.size)

/-- An actual affine normalization slice algebra. No basis of the original
projective module is chosen and all original linear relations survive. -/
@[expose] def ideal : Ideal A := Ideal.span {x i-1}
abbrev algebra := A ⧸ ideal R P i

lemma coordinate_one : Ideal.Quotient.mk (ideal R P i) (x i)=1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (ideal R P i)),← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

variable (S : Type w) [CommRing S] [Algebra R S]
@[expose] def forward (a : algebra R P i →ₐ[R] S) :
    ProjectiveParameterUnitSlice318.SlicePoint R P S i :=
  ⟨a.comp (Ideal.Quotient.mkₐ R (ideal R P i)),by
    change a (Ideal.Quotient.mk (ideal R P i) (x i))=1
    rw [coordinate_one,map_one]⟩

lemma kernel (a : ProjectiveParameterUnitSlice318.SlicePoint R P S i) :
    ideal R P i ≤ RingHom.ker a.val.toRingHom := by
  apply Ideal.span_le.mpr
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  change a.val (x i-1)=0
  rw [map_sub,a.property,map_one,sub_self]

@[expose] def backward (a : ProjectiveParameterUnitSlice318.SlicePoint R P S i) :
    algebra R P i →ₐ[R] S :=
  Ideal.Quotient.liftₐ (ideal R P i) a.val (fun z hz => kernel R P i S a hz)

/-- The normalized slice is represented by the SAME symmetric parameter
algebra modulo its literal coordinate-minus-one relation. -/
@[expose] def points : (algebra R P i →ₐ[R] S) ≃
    ProjectiveParameterUnitSlice318.SlicePoint R P S i where
  toFun := forward R P i S
  invFun := backward R P i S
  left_inv a := by
    apply AlgHom.ext
    intro z
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.lift (ideal R P i)
      (a.comp (Ideal.Quotient.mkₐ R (ideal R P i))).toRingHom _
      (Ideal.Quotient.mk (ideal R P i) y)=a (Ideal.Quotient.mk (ideal R P i) y)
    rw [Ideal.Quotient.lift_mk]
    rfl
  right_inv a := by
    apply Subtype.ext
    exact Ideal.Quotient.liftₐ_comp (ideal R P i) a.val _

/-- On each ACTUAL principal parameter chart, the point functor splits
as a coefficient unit times a represented affine slice. This is a local
quotient construction, not yet the globally glued projective parameter. -/
@[expose] def chartPoints : ProjectiveParameterUnitSlice318.ChartPoint R P S i ≃
    Sˣ × (algebra R P i →ₐ[R] S) :=
  (ProjectiveParameterUnitSlice318.trivialization R P S i).trans
    (Equiv.prodCongr (Equiv.refl _) (points R P i S).symm)
end ProjectiveParameterSliceAlgebra318
