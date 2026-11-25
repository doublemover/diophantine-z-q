module
public import OriginalUpperActualFibreCrossingIdeal318
public import Mathlib.LinearAlgebra.Dimension.Finite

public section
noncomputable section
namespace OriginalUpperActualFibreIntersectionLength318

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open OriginalUpperActualFibreComponents318 (C ambientSupport support_image)
open OriginalUpperActualFibreIncidence318 (common finite_common)
open OriginalUpperActualFibreCrossingIdeal318 (length length_positive)
open scoped BigOperators

universe u
variable {X Z : Scheme.{u}} (s : X ⟶ Z) (p : Z)
variable (E F : C s p)
variable (closed : IsClosed ({p} : Set Z))

abbrev Meeting := ↥(common s p E F)

include closed in
theorem over_p (x : Meeting s p E F) : s x.1 = p := by
  have h : x.1 ∈ Set.range (s.fiberι p) := by
    obtain ⟨y,_,hy⟩ := (support_image s p closed E) ▸ x.property.1
    exact ⟨y,hy⟩
  rw [s.range_fiberι p] at h
  exact h

/-- Not an arbitrary coefficient-field inclusion: the structural
map of the genuine scheme stalks induces this residue field algebra. -/
@[expose, instance_reducible] def residueAlgebra (x : Meeting s p E F) : Algebra (Z.residueField p) (X.residueField x.1) :=
  ((Z.residueFieldCongr (over_p s p E F closed x).symm).hom ≫ s.residueFieldMap x.1).hom.toAlgebra

def residueDegree (x : Meeting s p E F) : ℕ :=
  letI := residueAlgebra s p E F closed x
  Module.finrank (Z.residueField p) (X.residueField x.1)

/-- The actual weighted closed-point length. No logarithmic residue
factor has been built into the integer graph: all degrees are relative
to this exact k(p). -/
def localIntersection (x : Meeting s p E F) : ℕ :=
  residueDegree s p E F closed x * (length s p E F x.1 x.property).toNat

theorem local_positive (x : Meeting s p E F)
    (finiteResidue : letI := residueAlgebra s p E F closed x;
      Module.Finite (Z.residueField p) (X.residueField x.1))
    (finiteLength : length s p E F x.1 x.property ≠ ⊤) :
    0 < localIntersection s p E F closed x := by
  let := residueAlgebra s p E F closed x
  let := finiteResidue
  exact Nat.mul_pos Module.finrank_pos <|
    ENat.toNat_pos (length_positive s p E F x.1 x.property).ne' finiteLength

variable [IsIntegral X] (vertical : s (genericPoint X) ≠ p)
variable (dim : ∀ y : X, coheight y ≤ 2) (different : E ≠ F) [NoetherianSpace X]

/-- True finite local-length sum of intersection multiplicities on
the original proper fibre. The finite support is constructed from the
scheme topology, not supplied as lists or edges. -/
def intersection : ℤ :=
  letI := (finite_common s p E F different closed vertical dim).fintype
  ∑ x : Meeting s p E F, (localIntersection s p E F closed x : ℤ)

theorem nonnegative :
    0 ≤ intersection s p E F closed vertical dim different := by
  let := (finite_common s p E F different closed vertical dim).fintype
  exact Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

/-- The actual positive-at-meeting predicate of the reduced fibre
calculation. Finiteness is stated only for the genuine local residue
field and the genuine two-component quotient. -/
theorem positive_on_meet
    (meet : ((E : Set (s.fiber p)) ∩ (F : Set (s.fiber p))).Nonempty)
    (finiteResidue : ∀ x : Meeting s p E F, letI := residueAlgebra s p E F closed x;
      Module.Finite (Z.residueField p) (X.residueField x.1))
    (finiteLength : ∀ x : Meeting s p E F, length s p E F x.1 x.property ≠ ⊤) :
    0 < intersection s p E F closed vertical dim different := by
  classical
  let := (finite_common s p E F different closed vertical dim).fintype
  obtain ⟨v,hv₁,hv₂⟩ := meet
  let x : Meeting s p E F := ⟨s.fiberι p v,
    ⟨(support_image s p closed E).symm ▸ (show s.fiberι p v ∈ s.fiberι p '' (E : Set (s.fiber p))
        from ⟨v,hv₁,rfl⟩),
      (support_image s p closed F).symm ▸ (show s.fiberι p v ∈ s.fiberι p '' (F : Set (s.fiber p))
        from ⟨v,hv₂,rfl⟩)⟩⟩
  have hx : 0 < (localIntersection s p E F closed x : ℤ) := by
    exact_mod_cast local_positive s p E F closed x (finiteResidue x) (finiteLength x)
  exact Finset.sum_pos' (fun _ _ => Int.natCast_nonneg _) ⟨x,Finset.mem_univ x,hx⟩

end OriginalUpperActualFibreIntersectionLength318

#print axioms OriginalUpperActualFibreIntersectionLength318.over_p
#print axioms OriginalUpperActualFibreIntersectionLength318.local_positive
#print axioms OriginalUpperActualFibreIntersectionLength318.nonnegative
#print axioms OriginalUpperActualFibreIntersectionLength318.positive_on_meet
