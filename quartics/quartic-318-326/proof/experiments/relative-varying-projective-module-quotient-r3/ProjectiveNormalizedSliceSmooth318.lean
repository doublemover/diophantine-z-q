module
public import ProjectiveNormalizedLinearLift318
public section
noncomputable section
namespace ProjectiveNormalizedSliceSmooth318
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  [Module.Projective R M] (m : M)
local notation "A" => SymmetricAlgebra R M
@[expose] def ideal : Ideal A := Ideal.span {SymmetricAlgebra.ι R M m-1}
abbrev algebra := A ⧸ ideal R M m

lemma coordinate_one : Ideal.Quotient.mk (ideal R M m) (SymmetricAlgebra.ι R M m)=1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (ideal R M m)),← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- A normalized slice of the symmetric algebra of a PROJECTIVE module
is formally smooth over the original arbitrary base. The lifting proof
constructs a normalized actual linear functional and its quotient map;
finite presentation and a scheme-level smoothness claim remain separate. -/
instance formallySmooth : Algebra.FormallySmooth R (algebra R M m) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro S _ _ I hI f
  let q := Ideal.Quotient.mkₐ R I
  let a := f.comp (Ideal.Quotient.mkₐ R (ideal R M m))
  let l := a.toLinearMap.comp (SymmetricAlgebra.ι R M)
  have hm : l m=1 := by
    change f (Ideal.Quotient.mk (ideal R M m) (SymmetricAlgebra.ι R M m))=1
    rw [coordinate_one,map_one]
  obtain ⟨g,hg,hgm⟩ := ProjectiveNormalizedLinearLift318.exists_normalized_lift R M m S I hI l hm
  let b : A →ₐ[R] S := SymmetricAlgebra.lift g
  have hb : ideal R M m≤RingHom.ker b.toRingHom := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change b (SymmetricAlgebra.ι R M m-1)=0
    rw [map_sub,map_one]
    change SymmetricAlgebra.lift g (SymmetricAlgebra.ι R M m)-1=0
    rw [SymmetricAlgebra.lift_ι_apply,hgm,sub_self]
  let h : algebra R M m →ₐ[R] S := Ideal.Quotient.liftₐ (ideal R M m) b hb
  refine ⟨h,?_⟩
  apply Ideal.Quotient.algHom_ext
  apply SymmetricAlgebra.algHom_ext
  ext x
  change q (b (SymmetricAlgebra.ι R M x))=a (SymmetricAlgebra.ι R M x)
  change q (SymmetricAlgebra.lift g (SymmetricAlgebra.ι R M x))=l x
  rw [SymmetricAlgebra.lift_ι_apply]
  exact LinearMap.congr_fun hg x
end ProjectiveNormalizedSliceSmooth318
