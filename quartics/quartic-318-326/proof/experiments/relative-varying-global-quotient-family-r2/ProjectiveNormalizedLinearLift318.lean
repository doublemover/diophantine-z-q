module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Smooth.Basic
public section
noncomputable section
namespace ProjectiveNormalizedLinearLift318
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  [Module.Projective R M] (m : M)
  (S : Type w) [CommRing S] [Algebra R S] (I : Ideal S) (hI : I^2=⊥)
  (f : M →ₗ[R] S ⧸ I) (hm : f m=1)

/-- Lift the actual linear functional through the square-zero quotient,
then normalize its original marked vector by a genuine lifted unit. No
free basis or reduced coefficient ring is assumed. -/
lemma exists_normalized_lift : ∃ g : M →ₗ[R] S,
    (Ideal.Quotient.mkₐ R I).toLinearMap.comp g=f ∧ g m=1 := by
  let q := Ideal.Quotient.mkₐ R I
  obtain ⟨l,hl⟩ := Module.projective_lifting_property q.toLinearMap f Ideal.Quotient.mk_surjective
  have ha : q (l m)=1 := (LinearMap.congr_fun hl m).trans hm
  have hu : IsUnit (l m) := (IsNilpotent.isUnit_quotient_mk_iff ⟨2,hI⟩).mp (by
    change IsUnit (q (l m))
    rw [ha]
    exact isUnit_one)
  let u : Sˣ := hu.unit
  have huval : (u:S)=l m := hu.unit_spec
  have hi : q ((u⁻¹:Sˣ):S)=1 := by
    have h := congrArg q (Units.inv_mul u)
    rw [map_mul,map_one,huval,ha,mul_one] at h
    exact h
  refine ⟨((u⁻¹:Sˣ):S) • l,?_,?_⟩
  · ext x
    change q (((u⁻¹:Sˣ):S)*l x)=f x
    rw [map_mul,hi,one_mul]
    exact LinearMap.congr_fun hl x
  · change ((u⁻¹:Sˣ):S)*l m=1
    rw [← huval,Units.inv_mul]
end ProjectiveNormalizedLinearLift318
