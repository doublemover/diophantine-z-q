module
public import ComplexPolynomialOpenPoints318
public import BasePreservingAffinePoints318
public section
noncomputable section
namespace LocalizedComplexPointBase318
open ComplexPolynomialOpenPoints318
variable {ι : Type} {A : Type} [CommRing A] [Algebra ℂ A]
variable (g : MvPolynomial ι ℂ →ₐ[ℂ] A) (d : MvPolynomial ι ℂ)

/-- Every ordinary complex algebra point of the WHOLE localized source
has an actual base vector, nonzero d there and the full base-localization
square. Base preservation is constructed, not assumed as an extra point
condition. -/
theorem exists_base (f : Localization.Away (g d) →ₐ[ℂ] ℂ) :
    ∃ v : ι → ℂ, ∃ hv : MvPolynomial.eval v d ≠ 0,
      f.toRingHom.comp (Localization.awayMap g.toRingHom d) = evaluation d v hv := by
  let φ : MvPolynomial ι ℂ →+* ℂ :=
    f.toRingHom.comp ((algebraMap A (Localization.Away (g d))).comp g.toRingHom)
  let v : ι → ℂ := fun i => φ (MvPolynomial.X i)
  have hφ : φ = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change f (algebraMap A (Localization.Away (g d)) (g (MvPolynomial.C c))) = c
      rw [show g (MvPolynomial.C c) = algebraMap ℂ A c from g.commutes c,
        ←IsScalarTower.algebraMap_apply ℂ A (Localization.Away (g d))]
      exact f.commutes c
    · intro i
      rw [MvPolynomial.eval_X]
      rfl
  have hfd : f (algebraMap A (Localization.Away (g d)) (g d)) = MvPolynomial.eval v d :=
    congrArg (fun h : MvPolynomial ι ℂ →+* ℂ => h d) hφ
  have hv : MvPolynomial.eval v d ≠ 0 := by
    intro hz
    have h := congrArg f (IsLocalization.Away.mul_invSelf (g d) (S := Localization.Away (g d)))
    rw [map_mul,map_one,hfd,hz,zero_mul] at h
    exact zero_ne_one h
  refine ⟨v,hv,?_⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  ext p
  simp only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq,evaluation_source]
  exact congrArg (fun h : MvPolynomial ι ℂ →+* ℂ => h p) hφ
end LocalizedComplexPointBase318
