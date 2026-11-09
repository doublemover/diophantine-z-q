module
public import ThreeJReciprocalKernelCertificate318
public section
noncomputable section
namespace AffineIdealCoordinates318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {A : Type u} [CommRing A]

@[expose] def coordinates (I : (Spec (CommRingCat.of A)).IdealSheafData) : Ideal A :=
  (I.ideal ⟨⊤,isAffineOpen_top (Spec (CommRingCat.of A))⟩).comap
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The actual ideal-sheaf support and its canonical affine-coordinate
ideal have exactly the same scheme-prime zero locus. -/
theorem support_coordinates (I : (Spec (CommRingCat.of A)).IdealSheafData) :
    (I.support : Set (Spec (CommRingCat.of A)))=PrimeSpectrum.zeroLocus (coordinates I : Set A) := by
  have he : Scheme.IdealSheafData.ofIdealTop
      (I.ideal ⟨⊤,isAffineOpen_top (Spec (CommRingCat.of A))⟩)=I :=
    Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply I
  calc
    _ = ((Scheme.IdealSheafData.ofIdealTop
      (I.ideal ⟨⊤,isAffineOpen_top (Spec (CommRingCat.of A))⟩)).support : Set _) :=
      congrArg (fun J : (Spec (CommRingCat.of A)).IdealSheafData => (J.support : Set _)) he.symm
    _ = _ := by
      rw [Scheme.IdealSheafData.coe_support_ofIdealTop,Scheme.Spec_zeroLocus]
      rfl

/-- Support contained in D(x) supplies a genuine inverse for x modulo the
whole ideal. This is stronger than merely excluding a rational point. -/
theorem quotient_unit_of_support (I : Ideal A) (x : A)
    (h : PrimeSpectrum.zeroLocus (I : Set A) ⊆ PrimeSpectrum.basicOpen x) :
    IsUnit (Ideal.Quotient.mk I x) := by
  have hz : PrimeSpectrum.zeroLocus ((I ⊔ Ideal.span {x} : Ideal A) : Set A)=∅ := by
    rw [PrimeSpectrum.zeroLocus_sup,PrimeSpectrum.zeroLocus_span]
    apply Set.eq_empty_iff_forall_not_mem.mpr
    rintro p ⟨hp,hx⟩
    exact h hp (hx (Set.mem_singleton x))
  have ht : I ⊔ Ideal.span {x}=⊤ := PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp hz
  have h1 : (1:A) ∈ I ⊔ Ideal.span {x} := by rw [ht];trivial
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hb
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk I c,?_⟩
  have he := congrArg (Ideal.Quotient.mk I) hab
  have ha0 : Ideal.Quotient.mk I a=0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [←hc,map_add,map_mul,map_one,ha0,zero_add] at he
  exact he
end AffineIdealCoordinates318
