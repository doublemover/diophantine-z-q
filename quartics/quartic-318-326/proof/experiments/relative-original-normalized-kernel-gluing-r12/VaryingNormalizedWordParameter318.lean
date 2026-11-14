module
public import VaryingSourceWordOpen318
public section
noncomputable section
namespace VaryingNormalizedWordParameter318
open VaryingMatrixWords318 VaryingSourcePointNaturality318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
local notation "B" => VaryingSourceActionParameter318.ring R A ι
@[expose] def relation (ij : ι × ι) : B :=
  columns (VaryingSourceWordOpen318.universal R A ι).val w ij.1 ij.2 -
    (1 : Matrix ι ι B) ij.1 ij.2
@[expose] def ideal : Ideal B := Ideal.span (Set.range (relation R A ι w))
abbrev ring := B ⧸ ideal R A ι w
abbrev quotient : B →ₐ[R] ring R A ι w := Ideal.Quotient.mkₐ R (ideal R A ι w)

variable (S : Type u) [CommRing S] [Algebra R S]
lemma word_forward (f : B →ₐ[R] S) (l : List A) (i : ι) :
    f (wordVector (VaryingSourceWordOpen318.universal R A ι).val l i)=
      wordVector (VaryingSourceActionParameter318.toPoint R A ι S f).val l i := by
  have h := toPoint_natural R A ι B S f (AlgHom.id R B)
  simp only [AlgHom.comp_id] at h
  rw [h]
  exact wordVector_map R f (VaryingSourceWordOpen318.universal R A ι).val l i

lemma evaluate_relation (f : B →ₐ[R] S) (ij : ι × ι) :
    f (relation R A ι w ij)=
      columns (VaryingSourceActionParameter318.toPoint R A ι S f).val w ij.1 ij.2 -
        (1 : Matrix ι ι S) ij.1 ij.2 := by
  simp only [relation,columns,map_sub,word_forward,Matrix.one_apply]
  split_ifs <;> simp

/-- The word frame is fixed exactly, not merely required to be invertible. -/
abbrev Point := {d : VaryingSourceActionParameter318.Point R A ι S // columns d.val w=1}
@[expose] def toPoint (f : ring R A ι w →ₐ[R] S) : Point R A ι w S :=
  ⟨VaryingSourceActionParameter318.toPoint R A ι S (f.comp (quotient R A ι w)),by
    ext i j
    apply sub_eq_zero.mp
    rw [← evaluate_relation]
    change f (quotient R A ι w (relation R A ι w (i,j)))=0
    rw [show quotient R A ι w (relation R A ι w (i,j))=0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self (i,j))),map_zero]⟩
@[expose] def fromPoint (d : Point R A ι w S) : ring R A ι w →ₐ[R] S :=
  Ideal.Quotient.liftₐ (ideal R A ι w)
    (VaryingSourceActionParameter318.fromPoint R A ι S d.val) (by
      have h : ideal R A ι w ≤ RingHom.ker
          (VaryingSourceActionParameter318.fromPoint R A ι S d.val).toRingHom := by
        apply Ideal.span_le.mpr
        rintro x ⟨ij,rfl⟩
        change VaryingSourceActionParameter318.fromPoint R A ι S d.val
          (relation R A ι w ij)=0
        rw [evaluate_relation]
        change columns
          ((VaryingSourceActionParameter318.pointsWithRelations R A ι S)
            ((VaryingSourceActionParameter318.pointsWithRelations R A ι S).symm d.val)).val
          w ij.1 ij.2-(1 : Matrix ι ι S) ij.1 ij.2=0
        rw [Equiv.apply_symm_apply,d.property,sub_self]
      exact fun x hx => h hx)
lemma fromPoint_quotient (d : Point R A ι w S) (z : B) :
    fromPoint R A ι w S d (quotient R A ι w z)=
      VaryingSourceActionParameter318.fromPoint R A ι S d.val z :=
  Ideal.Quotient.lift_mk _ _ _

/-- The explicit source-relation quotient represents all normalized word
frames on arbitrary coefficient rings, including nilpotents. -/
@[expose] def points : (ring R A ι w →ₐ[R] S) ≃ Point R A ι w S where
  toFun := toPoint R A ι w S
  invFun := fromPoint R A ι w S
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    ext z
    rw [AlgHom.comp_apply,fromPoint_quotient]
    exact congrArg (fun g : B →ₐ[R] S => g z)
      ((VaryingSourceActionParameter318.pointsWithRelations R A ι S).symm_apply_apply
        (f.comp (quotient R A ι w)))
  right_inv d := by
    apply Subtype.ext
    have h : (fromPoint R A ι w S d).comp (quotient R A ι w)=
        VaryingSourceActionParameter318.fromPoint R A ι S d.val := by
      ext z
      exact fromPoint_quotient R A ι w S d z
    change VaryingSourceActionParameter318.toPoint R A ι S
      ((fromPoint R A ι w S d).comp (quotient R A ι w))=d.val
    rw [h]
    exact (VaryingSourceActionParameter318.pointsWithRelations R A ι S).apply_symm_apply d.val
end VaryingNormalizedWordParameter318
