module
public import ContactBoundedHilbertBaseChange318
public section
noncomputable section
namespace ContactBoundedRankCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactBoundedSchemeHilbertData318.Data c N b)
local notation "π" => ContactBoundedSchemeHilbertData318.projection c N b D
/-- The rank decomposition is DERIVED from finite flat finite
presentation of the actual whole family. -/
@[expose] def locus (d : Fin (N+1)) : B.Opens :=
  ⟨{x | π.finrank x=d.val},(π.isLocallyConstant_finrank.isClopen_fiber d.val).2⟩
lemma closed (d : Fin (N+1)) : IsClosed (locus c N b D d : Set B) :=
  (π.isLocallyConstant_finrank.isClopen_fiber d.val).1
abbrev into (d : Fin (N+1)) := (locus c N b D d).ι
lemma rank (d : Fin (N+1)) (x : locus c N b D d) : π.finrank (into c N b D d x)=d.val := x.property
@[expose] def cover : B.OpenCover where
  I₀ := Fin (N+1)
  X d := (locus c N b D d).toScheme
  f := into c N b D
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun d => inferInstance⟩
    intro x
    let d : Fin (N+1) := ⟨π.finrank x,Nat.lt_succ_of_le (D.bound x)⟩
    exact ⟨d,⟨x,rfl⟩,rfl⟩
/-- Distinct rank pieces have EMPTY categorical intersections. -/
lemma intersection_empty (d e : Fin (N+1)) (h : d≠e) :
    IsEmpty (pullback (into c N b D d) (into c N b D e)) := by
  refine ⟨fun x => h (Fin.ext ?_)⟩
  have hp := congrArg (fun k : pullback (into c N b D d) (into c N b D e) ⟶ B => k x)
    (pullback.condition (f := into c N b D d) (g := into c N b D e))
  exact (rank c N b D d _).symm.trans ((congrArg π.finrank hp).trans (rank c N b D e _))
end ContactBoundedRankCover318
