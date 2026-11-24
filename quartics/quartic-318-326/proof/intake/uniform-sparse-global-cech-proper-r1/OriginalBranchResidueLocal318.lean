module
public import OriginalBranchPlaneLocal318
public section
noncomputable section
namespace OriginalBranchResidueLocal318
open OriginalBranchPlaneLocal318 Polynomial
variable {k : Type*} [Field k] {I : Ideal (Plane (k:=k))}
abbrev stalk (φ : A I→ₐ[k]k) := Localization.AtPrime (pointPrime I φ)
@[expose] def toLocal (φ : A I→ₐ[k]k) : A I→+*stalk φ := algebraMap _ _
@[expose] def specialize (φ : A I→ₐ[k]k) : stalk φ→+*k :=
  IsLocalization.lift (M:=(pointPrime I φ).primeCompl) (g:=φ.toRingHom)
    (fun a => isUnit_iff_ne_zero.mpr (show φ a≠0 from a.property))
theorem specialize_local (φ : A I→ₐ[k]k) (a : A I) : specialize φ (toLocal φ a)=φ a :=
  IsLocalization.lift_eq _ _
theorem unit_at (φ : A I→ₐ[k]k) (a : A I) (h : φ a≠0) : IsUnit (toLocal φ a) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (stalk φ) (pointPrime I φ) a).mpr h
@[expose] def invAt (φ : A I→ₐ[k]k) (a : A I) (h : φ a≠0) : stalk φ :=
  ↑(unit_at φ a h).unit⁻¹
theorem inverse_spec (φ : A I→ₐ[k]k) (a : A I) (h : φ a≠0) :
    toLocal φ a*invAt φ a h=1 := (unit_at φ a h).mul_val_inv
theorem inverse_read (φ : A I→ₐ[k]k) (a : A I) (h : φ a≠0) :
    specialize φ (invAt φ a h)=(φ a)⁻¹ := by
  have e:=congrArg (specialize φ) (inverse_spec φ a h)
  rw [map_mul,map_one,specialize_local] at e
  calc
    _ = (φ a)⁻¹*(φ a * specialize φ (invAt φ a h)) := by rw [←mul_assoc,inv_mul_cancel₀ h,one_mul]
    _ = _ := by rw [e,mul_one]

/-- This is the REGULAR numerator of the possible simple pole in the y-frame,
as a literal element of the genuine local ring, not a numerical prescription. -/
@[expose] def principalNumerator (φ : A I→ₐ[k]k) (x : A I) (F G : k[X]) (i j : ℕ)
    (h : φ (aeval x F.derivative)≠0) : stalk φ :=
  -2*(toLocal φ x)^(i+j)*(toLocal φ (aeval x G))*(invAt φ (aeval x F.derivative) h)^2
theorem principal_read (φ : A I→ₐ[k]k) (x : A I) (F G : k[X]) (i j : ℕ)
    (h : φ (aeval x F.derivative)≠0) :
    specialize φ (principalNumerator φ x F G i j h)=
    -2*(φ x)^(i+j)*G.eval (φ x)/(F.derivative.eval (φ x))^2 := by
  have he (P : k[X]) : φ (aeval x P) = P.eval (φ x) := by
    rw [←aeval_algHom_apply,aeval_def,Algebra.algebraMap_self,eval₂_id]
  have h2 : specialize φ (-2) = -2 := by
    have hh := map_neg (specialize φ) (2:stalk φ)
    rw [map_ofNat] at hh
    exact hh
  rw [principalNumerator,map_mul,map_mul,map_mul,map_pow,map_pow,specialize_local,specialize_local,inverse_read,he,he,h2]
  simp only [div_eq_mul_inv,inv_pow]
end OriginalBranchResidueLocal318
#print axioms OriginalBranchResidueLocal318.principal_read
