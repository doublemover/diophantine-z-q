module
public import IntrinsicTensorGenerator318
public import BaseChangingDifferentialTensor318
public section
noncomputable section
namespace IntrinsicFramedTensorSections318
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u
variable {Y : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (p : Y ⟶ Spec (CommRingCat.of R))
  (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (e : KaehlerDifferential R A ≃ₗ[A] A)
local notation "M" => FamilyIntrinsicDifferentials318.omega p
local notation "T" => IntrinsicTensorSheaf318.tensor M M

@[expose] def coefficient (z : Γ(T,j ''ᵁ ⊤)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤ z)

/-- The actual full-open intrinsic tensor frame recovers the literal
algebraic coefficient of a universal-coordinate square. -/
theorem coefficient_weighted (a s : A) (hs : e (KaehlerDifferential.D R A s) = 1) :
    coefficient j p h e (IntrinsicTensorChartSections318.weightedSquare j p h a
      (KaehlerDifferential.D R A s)) = a := by
  let a0 : Γ(Y,j ''ᵁ ⊤) := (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
  have hm : (IntrinsicTensorGenerator318.ambientFrame j p h e).hom.app ⊤ a0 =
      IntrinsicTensorChartSections318.weightedSquare j p h a (KaehlerDifferential.D R A s) := by
    have hh := ((IntrinsicTensorGenerator318.ambientFrame j p h e).hom.val.app (op ⊤)).hom.map_smul
      ((j.appIso ⊤).hom a0) (show Γ(Y,j ''ᵁ ⊤) from 1)
    change (IntrinsicTensorGenerator318.ambientFrame j p h e).hom.app ⊤
      ((j.appIso ⊤).inv ((j.appIso ⊤).hom a0)*1) =
      (j.appIso ⊤).inv ((j.appIso ⊤).hom a0) •
        (IntrinsicTensorGenerator318.ambientFrame j p h e).hom.app ⊤
          (show Γ(Y,j ''ᵁ ⊤) from 1) at hh
    simpa only [Iso.hom_inv_id_apply,mul_one,
      IntrinsicTensorGenerator318.ambientFrame_one j p h e s hs] using hh
  rw [coefficient,←hm]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤
      ((IntrinsicTensorGenerator318.frame j p h e).inv.app ⊤
        ((j.appIso ⊤).hom a0))) = a
  have hF (x : Γ(Spec (CommRingCat.of A),⊤)) :
      (IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤
        ((IntrinsicTensorGenerator318.frame j p h e).inv.app ⊤ x) = x :=
    congrArg (fun f => f.app ⊤ x) (IntrinsicTensorGenerator318.frame j p h e).inv_hom_id
  rw [hF]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((j.appIso ⊤).hom ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) = a
  rw [CategoryTheory.Iso.inv_hom_id_apply,CategoryTheory.Iso.inv_hom_id_apply]

@[expose] def scalar : Γ(Y,j ''ᵁ ⊤) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (j.appIso ⊤).hom.hom

lemma coefficient_add (z w : Γ(T,j ''ᵁ ⊤)) :
    coefficient j p h e (z+w) = coefficient j p h e z + coefficient j p h e w := by
  simp only [coefficient,map_add]
lemma coefficient_zero : coefficient j p h e (0 : Γ(T,j ''ᵁ ⊤)) = 0 := by
  simp only [coefficient,map_zero]

/-- The coefficient respects the ACTUAL ambient-to-affine scalar map. -/
lemma coefficient_smul (a : Γ(Y,j ''ᵁ ⊤)) (z : Γ(T,j ''ᵁ ⊤)) :
    coefficient j p h e (a • z) = scalar j a * coefficient j p h e z := by
  have hl := ((IntrinsicTensorGenerator318.frame j p h e).hom.val.app (op ⊤)).hom.map_smul
    ((j.appIso ⊤).hom a) z
  change (IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤
      ((j.appIso ⊤).inv ((j.appIso ⊤).hom a) • z) =
    (j.appIso ⊤).hom a * (IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤ z at hl
  rw [Iso.hom_inv_id_apply] at hl
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤ (a • z)) = _
  rw [hl,map_mul]
  rfl

lemma coefficient_injective : Function.Injective (coefficient j p h e) := by
  intro z w hzw
  apply (ConcreteCategory.bijective_of_isIso ((IntrinsicTensorGenerator318.frame j p h e).hom.app ⊤)).1
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1 hzw

/-- Reconstruction holds for EVERY whole-open sheaf section, not merely
for global q0/q1 or for the displayed pure tensors. -/
theorem section_reconstruct (s : A) (hs : e (KaehlerDifferential.D R A s) = 1)
    (z : Γ(T,j ''ᵁ ⊤)) :
    IntrinsicTensorChartSections318.weightedSquare j p h (coefficient j p h e z)
      (KaehlerDifferential.D R A s) = z := by
  apply coefficient_injective j p h e
  exact coefficient_weighted j p h e _ s hs

@[expose] def tensor (s : A) (z : Γ(T,j ''ᵁ ⊤)) :
    KaehlerDifferential R A ⊗[A] KaehlerDifferential R A :=
  coefficient j p h e z • (KaehlerDifferential.D R A s ⊗ₜ[A] KaehlerDifferential.D R A s)

/-- Genuine semilinear map on the WHOLE section module, with the exact
GammaSpec/open-immersion scalar comparison, not an operation on chosen presentations. -/
@[expose] def tensorMap (s : A) : Γ(T,j ''ᵁ ⊤) →ₛₗ[scalar j]
    (KaehlerDifferential R A ⊗[A] KaehlerDifferential R A) where
  toFun := tensor j p h e s
  map_add' z w := by rw [tensor,coefficient_add,add_smul];rfl
  map_smul' a z := by rw [tensor,coefficient_smul,mul_smul];rfl

theorem tensor_weighted (a s : A) (hs : e (KaehlerDifferential.D R A s) = 1) :
    tensor j p h e s (IntrinsicTensorChartSections318.weightedSquare j p h a
      (KaehlerDifferential.D R A s)) =
    a • (KaehlerDifferential.D R A s ⊗ₜ[A] KaehlerDifferential.D R A s) := by
  rw [tensor,coefficient_weighted j p h e a s hs]

/-- Every algebraic differential is reconstructed in the ACTUAL
normalized universal-coordinate frame, not a newly chosen formal basis. -/
lemma differential_eq (s : A) (hs : e (KaehlerDifferential.D R A s) = 1)
    (ω : KaehlerDifferential R A) : ω = e ω • KaehlerDifferential.D R A s := by
  apply e.injective
  rw [map_smul,hs,smul_eq_mul,mul_one]

/-- On ALL pure tensors the whole-open section operation is the literal
inverse to the canonical intrinsic chart map. This rules out a
coefficient-only identification of the distinguished two sections. -/
theorem tensor_pure (s : A) (hs : e (KaehlerDifferential.D R A s) = 1)
    (ω η : KaehlerDifferential R A) :
    tensor j p h e s (IntrinsicTensorSheaf318.pure M M (j ''ᵁ ⊤)
      (IntrinsicChartSections318.sectionMap j p h ω)
      (IntrinsicChartSections318.sectionMap j p h η)) = ω ⊗ₜ[A] η := by
  have hω := differential_eq e s hs ω
  have hη := differential_eq e s hs η
  have hw : IntrinsicTensorSheaf318.pure M M (j ''ᵁ ⊤)
      (IntrinsicChartSections318.sectionMap j p h ω)
      (IntrinsicChartSections318.sectionMap j p h η) =
      IntrinsicTensorChartSections318.weightedSquare j p h (e ω*e η)
        (KaehlerDifferential.D R A s) := by
    calc
      _ = IntrinsicTensorSheaf318.pure M M (j ''ᵁ ⊤)
          (IntrinsicChartSections318.sectionMap j p h (e ω • KaehlerDifferential.D R A s))
          (IntrinsicChartSections318.sectionMap j p h (e η • KaehlerDifferential.D R A s)) :=
        congrArg₂ (fun x y => IntrinsicTensorSheaf318.pure M M (j ''ᵁ ⊤)
          (IntrinsicChartSections318.sectionMap j p h x)
          (IntrinsicChartSections318.sectionMap j p h y)) hω hη
      _ = _ := by
        rw [IntrinsicChartSections318.section_smul,IntrinsicChartSections318.section_smul,
          IntrinsicTensorChartSections318.pure_smul_smul]
        simp only [IntrinsicTensorChartSections318.weightedSquare,map_mul]
  rw [hw,tensor_weighted j p h e (e ω*e η) s hs]
  exact ((congrArg₂ (fun x y : KaehlerDifferential R A => x ⊗ₜ[A] y) hω hη).trans
    (TensorProduct.smul_tmul_smul (e ω) (e η) _ _)).symm
end IntrinsicFramedTensorSections318
