module
public import IntrinsicChartNaturality318
public import IntrinsicTensorSheaf318
public section
noncomputable section
namespace IntrinsicTensorChartSections318
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- Exact bilinearity of pure tensors in the genuine sheaf tensor product. -/
theorem pure_smul_smul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (a b : Γ(X,U)) (m : Γ(M,U)) (n : Γ(N,U)) :
    IntrinsicTensorSheaf318.pure M N U (a • m) (b • n) =
      (a*b) • IntrinsicTensorSheaf318.pure M N U m n := by
  have ht := TensorProduct.smul_tmul_smul (R:=Γ(X,U)) a b m n
  exact (congrArg ((IntrinsicTensorSheaf318.unit M N).app (op U)) ht).trans
    (((IntrinsicTensorSheaf318.unit M N).app (op U)).hom.map_smul (a*b) _)

variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- A coefficient times the square of a chart differential, in the actual
ambient tensor-square sheaf over the image of that chart. -/
@[expose] def weightedSquare (a : S) (ω : KaehlerDifferential R S) :
    Γ(IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p), j ''ᵁ ⊤) :=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a) •
    IntrinsicTensorSheaf318.pure (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p) (j ''ᵁ ⊤)
      (IntrinsicChartSections318.sectionMap j p h ω)
      (IntrinsicChartSections318.sectionMap j p h ω)

theorem weightedSquare_smul (a s : S) (ω : KaehlerDifferential R S) :
    weightedSquare j p h a (s • ω)=weightedSquare j p h (a*s^2) ω := by
  unfold weightedSquare
  rw [IntrinsicChartSections318.section_smul,pure_smul_smul,smul_smul]
  congr 1
  simp only [map_mul,pow_two]

theorem weightedSquare_mul (a b : S) (ω : KaehlerDifferential R S) :
    weightedSquare j p h (a*b) ω =
      (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a) •
        weightedSquare j p h b ω := by
  unfold weightedSquare
  rw [map_mul,map_mul,mul_smul]

/-- A whole-ring cleared coefficient and differential relation give the
corresponding exact cleared equality of actual intrinsic tensor sections. -/
theorem weightedSquare_cleared (A b k : S) (ω δ : KaehlerDifferential R S)
    (hb : A*b=k^2) (hδ : δ=k • ω) :
    (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv A) •
      weightedSquare j p h b ω = weightedSquare j p h 1 δ := by
  rw [←weightedSquare_mul,hδ,weightedSquare_smul,one_mul,hb]

/-- Cancellation uses an actual unit on the entire common affine open. -/
theorem weightedSquare_agreement (A b k d l : S) (ω η δ : KaehlerDifferential R S)
    (hA : IsUnit A) (hb : A*b=k^2) (hd : A*d=l^2)
    (hδ : δ=k • ω) (hη : δ=l • η) :
    weightedSquare j p h b ω = weightedSquare j p h d η := by
  have hu := (hA.map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).map (j.appIso ⊤).inv.hom
  apply hu.smul_left_cancel.mp
  exact (weightedSquare_cleared j p h A b k ω δ hb hδ).trans
    (weightedSquare_cleared j p h A d l η δ hd hη).symm

variable {T : Type u} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (hT : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- Restriction along a genuine affine open map transports coefficient and
both differential factors by the actual algebra map. -/
theorem weightedSquare_restrict (a : S) (ω : KaehlerDifferential R S) :
    (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p)).presheaf.map
        (homOfLE (OpenChartSections318.imageLE
          (Spec.map (CommRingCat.ofHom f.toRingHom)) j)).op
      (weightedSquare j p h a ω) =
    weightedSquare (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) p hT
      (f a) (AlgHomDifferential318.map f ω) := by
  unfold weightedSquare
  rw [Scheme.Modules.map_smul,IntrinsicTensorSheaf318.pure_restrict,
    IntrinsicChartNaturality318.section_restrict f j p h hT,
    OpenChartSections318.affine_restriction]
  rfl
/-- The same actual restriction through a specified common-chart route. -/
theorem weightedSquare_restrict_to
    (jT : Spec (CommRingCat.of T) ⟶ Y) [IsOpenImmersion jT]
    (hC : jT ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (route : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j=jT)
    (himage : jT ''ᵁ ⊤ ≤ j ''ᵁ ⊤) (a : S) (ω : KaehlerDifferential R S) :
    (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE himage).op
      (weightedSquare j p h a ω) =
    weightedSquare jT p hC (f a) (AlgHomDifferential318.map f ω) := by
  subst jT
  exact weightedSquare_restrict j p h f hC a ω
end IntrinsicTensorChartSections318
