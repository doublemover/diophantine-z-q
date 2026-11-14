module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace AlgebraEquationQuotientPoints318
variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type} (e : ι → A)
@[expose] def ideal (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type} (e : ι → A) : Ideal A := Ideal.span (Set.range e)
abbrev algebra := A ⧸ ideal R A e
abbrev quotient : A →ₐ[R] algebra R A e := Ideal.Quotient.mkₐ R (ideal R A e)
variable (S : Type) [CommRing S] [Algebra R S]
abbrev Points := {a : A →ₐ[R] S // ∀ i,a (e i)=0}
lemma kernel (a : Points R A e S) : ideal R A e≤RingHom.ker a.val.toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact a.property i
@[expose] def forward (a : algebra R A e →ₐ[R] S) : Points R A e S :=
  ⟨a.comp (quotient R A e),by
    intro i
    change a (Ideal.Quotient.mk (ideal R A e) (e i))=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i)),map_zero]⟩
@[expose] def backward (a : Points R A e S) : algebra R A e →ₐ[R] S :=
  Ideal.Quotient.liftₐ (ideal R A e) a.val (fun x hx => kernel R A e S a hx)
/-- Actual quotient by all specified equations, on every coefficient ring. -/
@[expose] def points : (algebra R A e →ₐ[R] S) ≃ Points R A e S where
  toFun := forward R A e S
  invFun := backward R A e S
  left_inv a := by
    apply Ideal.Quotient.algHom_ext
    exact Ideal.Quotient.liftₐ_comp (ideal R A e) (a.comp (quotient R A e)) _
  right_inv a := by
    apply Subtype.ext
    exact Ideal.Quotient.liftₐ_comp (ideal R A e) a.val _
lemma backward_quotient (a : Points R A e S) :
    ((points R A e S).symm a).comp (quotient R A e)=a.val :=
  Ideal.Quotient.liftₐ_comp (ideal R A e) a.val _
variable {T : Type} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
@[expose] def map (a : Points R A e S) : Points R A e T :=
  ⟨g.comp a.val,by intro i; change g (a.val (e i))=0; rw [a.property,map_zero]⟩
lemma natural (a : algebra R A e →ₐ[R] S) :
    points R A e T (g.comp a)=map R A e S g (points R A e S a) := by
  apply Subtype.ext
  rfl
lemma backward_natural (a : Points R A e S) :
    (points R A e T).symm (map R A e S g a)=g.comp ((points R A e S).symm a) := by
  apply (points R A e T).injective
  rw [Equiv.apply_symm_apply,natural,Equiv.apply_symm_apply]

end AlgebraEquationQuotientPoints318
