module
public import OriginalMarkedChartSpecialization318
public section
noncomputable section
namespace OriginalOneRawMarkedGenerator318
open OriginalHodgeModuleOverlap318
open scoped TensorProduct Pointwise
variable {S U E H : Type*} [CommRing S] [CommRing U] [Field E] [Algebra S U]
    [Algebra U E] [Algebra S E] [IsScalarTower S U E] [AddCommGroup H] [Module S H]

/-- Covariance on ONE true local generator of the Hodge square suffices for
all marked inputs; no global generator of the Hodge determinant exists in
general. A single equality after substitution of t alone is not this test. -/
theorem covariance (F:H→ₗ[S]E) (φ:U⊗[S]H→ₗ[U]U) (basis:U⊗[S]H≃ₗ[U]U) (b:E)
    (one:algebraMap U E (φ (basis.symm 1))=b*read (C:=U) F (basis.symm 1)) :
    ∀h:H,algebraMap U E (φ (1⊗ₜ[S]h))=b*F h := by
  have eq (x:U⊗[S]H) : algebraMap U E (φ x)=b*read (C:=U) F x := by
    have rep : x=basis x • basis.symm 1 := by
      apply basis.injective
      rw [map_smul,basis.apply_symm_apply,smul_eq_mul,mul_one]
    conv_lhs => rw [rep,map_smul,smul_eq_mul,map_mul,one]
    conv_rhs => rw [rep,map_smul,Algebra.smul_def]
    ring
  intro h
  simpa only [read_tmul,one_smul] using eq (1⊗ₜ[S]h)
omit [Algebra S E] [IsScalarTower S U E] in
/-- If the integral marked raw image contains the rational discriminant,
its value on any primitive local generator survives *every* map to a
characteristic-zero field. Even injectivity of the trait map is unnecessary. -/
theorem survives [CharZero E] (φ:U⊗[S]H→ₗ[U]U) (basis:U⊗[S]H≃ₗ[U]U)
    (im:φ.range=(210:U) • (⊤:Submodule U U)) :
    algebraMap U E (φ (basis.symm 1))≠0 := by
  obtain ⟨h,eq⟩ : (210:U)∈φ.range := by
    rw [im]
    have e :(210:U) • (1:U)∈(210:U) • (⊤:Submodule U U) :=
      Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    simpa only [smul_eq_mul,mul_one] using e
  have rep : h=basis h • basis.symm 1 := by
    apply basis.injective; rw [map_smul,basis.apply_symm_apply,smul_eq_mul,mul_one]
  intro killed
  rw [rep,map_smul,smul_eq_mul] at eq
  have e := congrArg (algebraMap U E) eq
  rw [map_mul,killed,mul_zero,map_ofNat] at e
  exact (by norm_num : (0:E)≠210) e

end OriginalOneRawMarkedGenerator318
