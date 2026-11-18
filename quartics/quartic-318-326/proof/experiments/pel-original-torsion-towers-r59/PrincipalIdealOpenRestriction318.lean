module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import OpenScalarSheafNaturality318
public section
noncomputable section
namespace PrincipalIdealOpenRestriction318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}

/-- Actual ideal-sheaf pullback of a global ideal through an open
immersion. This is equality of full quasi-coherent ideal data. -/
lemma comap_ofIdealTop (f : X ⟶ Y) [IsOpenImmersion f] (I : Ideal Γ(Y,⊤)) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f=
      Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ofIdealTop_ideal,Scheme.IdealSheafData.ofIdealTop_ideal]
  let e := (f.appIso U.1).commRingCatIsoToRingEquiv
  change ((I.map (Y.presheaf.map (homOfLE le_top).op).hom).comap e.symm.toRingHom)=_
  rw [Ideal.comap_symm,Ideal.map_map,Ideal.map_map]
  congr 1
  ext r
  exact OpenScalarSheafNaturality318.global_appIso f r U.1

@[expose] def principal (r : Γ(X,⊤)) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {r})
lemma comap_principal (f : X ⟶ Y) [IsOpenImmersion f] (r : Γ(Y,⊤)) :
    (principal r).comap f=principal (f.appTop r) := by
  rw [principal,comap_ofIdealTop,Ideal.map_span]
  simp only [Set.image_singleton]
  rfl

lemma span_unit_mul {R : Type u} [CommRing R] (u : Rˣ) (r : R) :
    Ideal.span {u.val*r}=Ideal.span {r} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton r))
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have hm : (u⁻¹).val*(u.val*r) ∈ Ideal.span {u.val*r} :=
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
    simpa only [←mul_assoc,Units.inv_mul,one_mul] using hm
lemma principal_unit_mul (u : Γ(X,⊤)ˣ) (r : Γ(X,⊤)) : principal (u.val*r)=principal r := by
  rw [principal,span_unit_mul]

/-- The actual local zero subscheme, with its original multiplicities.
No radical or reduced subscheme is substituted. -/
abbrev zeroScheme (r : Γ(X,⊤)) : Scheme := (principal r).subscheme
abbrev inclusion (r : Γ(X,⊤)) : zeroScheme r ⟶ X := (principal r).subschemeι
instance (r : Γ(X,⊤)) : IsClosedImmersion (inclusion r) := inferInstance
end PrincipalIdealOpenRestriction318
