module
public import VaryingSourceActionEquations318
public section
noncomputable section
namespace VaryingSourceActionParameter318
open VaryingCommutingMatrixRing318 VaryingCommutingMatrixPoints318
open VaryingSourceActionEquations318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "B" => algebra R A ι
@[expose] def relation (t : Index R A ι) : B :=
  equation R A ι B (VaryingWordDeterminantOpen318.universal R A ι) t
@[expose] def ideal : Ideal B := Ideal.span (Set.range (relation R A ι))
abbrev ring := B ⧸ ideal R A ι
abbrev quotient : B →ₐ[R] ring R A ι := Ideal.Quotient.mkₐ R (ideal R A ι)

variable (S : Type u) [CommRing S] [Algebra R S]
lemma evaluate_relation (f : B →ₐ[R] S) (t : Index R A ι) :
    f (relation R A ι t)=equation R A ι S (forward R A ι S f) t := by
  change f (equation R A ι B (VaryingWordDeterminantOpen318.universal R A ι) t)=_
  rw [equation_map,← VaryingWordDeterminantOpen318.forward_universal]

abbrev Point := {d : Data A ι S // Valid R A ι S d}
@[expose] def toPoint (f : ring R A ι →ₐ[R] S) : Point R A ι S :=
  ⟨forward R A ι S (f.comp (quotient R A ι)),by
    intro t
    rw [← evaluate_relation]
    change f (quotient R A ι (relation R A ι t))=0
    rw [show quotient R A ι (relation R A ι t)=0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self t)),map_zero]⟩

@[expose] def fromPoint (d : Point R A ι S) : ring R A ι →ₐ[R] S :=
  Ideal.Quotient.liftₐ (ideal R A ι) (backward R A ι S d.val) (by
    have h : ideal R A ι ≤ RingHom.ker (backward R A ι S d.val).toRingHom := by
      apply Ideal.span_le.mpr
      rintro x ⟨t,rfl⟩
      change backward R A ι S d.val (relation R A ι t)=0
      rw [evaluate_relation]
      change equation R A ι S ((points R A ι S) ((points R A ι S).symm d.val)) t=0
      rw [Equiv.apply_symm_apply]
      exact d.property t
    exact fun x hx => h hx)

lemma fromPoint_quotient (d : Point R A ι S) (z : B) :
    fromPoint R A ι S d (quotient R A ι z)=backward R A ι S d.val z :=
  Ideal.Quotient.lift_mk _ _ _

/-- The actual quotient of the SAME matrix-coordinate ring represents
all original source equations, with a marked vector, over every test ring. -/
@[expose] def pointsWithRelations : (ring R A ι →ₐ[R] S) ≃ Point R A ι S where
  toFun := toPoint R A ι S
  invFun := fromPoint R A ι S
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    ext z
    rw [AlgHom.comp_apply,fromPoint_quotient]
    exact congrArg (fun g : B →ₐ[R] S => g z)
      ((points R A ι S).symm_apply_apply (f.comp (quotient R A ι)))
  right_inv d := by
    apply Subtype.ext
    have h : (fromPoint R A ι S d).comp (quotient R A ι)=backward R A ι S d.val := by
      ext z
      exact fromPoint_quotient R A ι S d z
    change forward R A ι S ((fromPoint R A ι S d).comp (quotient R A ι))=d.val
    rw [h]
    exact (points R A ι S).apply_symm_apply d.val
end VaryingSourceActionParameter318
