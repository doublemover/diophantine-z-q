module
public import DerivationFromBasis318
public import AffineIntrinsicComparison318
public section
noncomputable section
namespace AffineBasicDerivation318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {S : CommRingCat.{u}} (M : (Spec S).Modules)
    (δ : S →+ Γ(M,⊤))
    (hδ : ∀ a b : S, δ (a*b)=a • δ b + b • δ a)

/-- Regard an additive global Leibniz map as an absolute derivation. Relative
coefficient vanishing is imposed after extension, without changing scalar data. -/
@[expose] def integralDerivation : Derivation ℤ S Γ(M,⊤) :=
  Derivation.mk' δ.toIntLinearMap hδ

/-- The actual S-linear restriction of module sections to an affine basic open. -/
@[expose] def restrictTop (s : S) : Γ(M,⊤) →ₗ[S] Γ(M,PrimeSpectrum.basicOpen s) :=
  ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE le_top).op).hom

/-- Extend the global derivation uniquely to the actual localized regular-function
ring of D(s), with values in the actual module sections on D(s). -/
@[expose] def basicDerivation (s : S) :
    Derivation ℤ Γ(Spec S,PrimeSpectrum.basicOpen s) Γ(M,PrimeSpectrum.basicOpen s) :=
  LocalizationDerivation318.extend (Submonoid.powers s)
    ((restrictTop M s).compDer (integralDerivation M δ hδ))

theorem basic_algebraMap (s a : S) :
    basicDerivation M δ hδ s (algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen s) a) =
      restrictTop M s (δ a) :=
  LocalizationDerivation318.extend_algebraMap _ _ a

/-- The localized derivations commute with every actual basic-open restriction.
Only agreement on S is needed; denominator cancellation gives all local sections. -/
theorem basic_naturality (s t : S) (h : PrimeSpectrum.basicOpen t ≤ PrimeSpectrum.basicOpen s)
    (a : Γ(Spec S,PrimeSpectrum.basicOpen s)) :
    basicDerivation M δ hδ t ((Spec S).presheaf.map (homOfLE h).op a) =
      M.val.map (homOfLE h).op (basicDerivation M δ hδ s a) := by
  let q : Γ(Spec S,PrimeSpectrum.basicOpen s) →+* Γ(Spec S,PrimeSpectrum.basicOpen t) :=
    ((Spec S).presheaf.map (homOfLE h).op).hom
  letI : Module Γ(Spec S,PrimeSpectrum.basicOpen s) Γ(M,PrimeSpectrum.basicOpen t) :=
    Module.compHom _ q
  letI : IsScalarTower S Γ(Spec S,PrimeSpectrum.basicOpen s) Γ(M,PrimeSpectrum.basicOpen t) := by
    refine IsScalarTower.of_algebraMap_smul ?_
    intro r m
    change q (algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen s) r) • m = r • m
    have hq : q (algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen s) r) =
        algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen t) r := by
      change (Spec S).presheaf.map (homOfLE h).op
        ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv r)) = _
      rw [←CommRingCat.comp_apply,←Functor.map_comp]
      rfl
    rw [hq,IsScalarTower.algebraMap_smul]
  have heq :
      (basicDerivation M δ hδ t).toLinearMap.toAddMonoidHom.comp q.toAddMonoidHom =
        (M.val.map (homOfLE h).op).hom.toAddMonoidHom.comp
          (basicDerivation M δ hδ s).toLinearMap.toAddMonoidHom := by
    apply LocalizationDerivation318.additive_ext (T:=Γ(Spec S,PrimeSpectrum.basicOpen s))
      (M:=Γ(M,PrimeSpectrum.basicOpen t)) (Submonoid.powers s)
    · intro b c
      change basicDerivation M δ hδ t (q (b*c)) = _
      rw [map_mul,Derivation.leibniz]
      rfl
    · intro b c
      change M.val.map (homOfLE h).op (basicDerivation M δ hδ s (b*c)) = _
      rw [Derivation.leibniz,map_add,M.val.map_smul,M.val.map_smul]
      rfl
    · intro r
      change basicDerivation M δ hδ t (q (algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen s) r)) = _
      have hq : q (algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen s) r) =
          algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen t) r := by
        change (Spec S).presheaf.map (homOfLE h).op
          ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv r)) = _
        rw [←CommRingCat.comp_apply,←Functor.map_comp]
        rfl
      rw [hq,basic_algebraMap]
      change restrictTop M t (δ r) =
        M.val.map (homOfLE h).op (basicDerivation M δ hδ s
          (algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen s) r))
      rw [basic_algebraMap]
      have hh := congrArg (fun k => k (δ r))
        ((modulesSpecToSheaf.obj M).presheaf.map_comp
          (homOfLE (show PrimeSpectrum.basicOpen s ≤ ⊤ from le_top)).op (homOfLE h).op)
      exact hh
  exact congrArg (fun f => f a) heq
end AffineBasicDerivation318
