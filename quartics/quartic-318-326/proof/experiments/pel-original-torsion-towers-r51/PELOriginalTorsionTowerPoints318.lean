module
public import PELOriginalDivisionTorsorIso318
public section
noncomputable section
namespace PELOriginalTorsionTowerPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalTorsionKernelScheme318
variable (τ : ℂ) (hτ : 0<τ.im) (m n : ℤ)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ))
/-- The original [m] map on full (mn)-torsion, on every scheme test. -/
@[expose] def down : torsion τ hτ (m*n) ρ →+ torsion τ hτ n ρ where
  toFun x := ⟨m • x.val,by rw [←mul_smul,mul_comm]; exact x.property⟩
  map_zero' := by apply Subtype.ext; exact zsmul_zero m
  map_add' x y := by apply Subtype.ext; exact zsmul_add x.val y.val m
/-- The honest inclusion of m-torsion into (mn)-torsion. -/
@[expose] def into : torsion τ hτ m ρ →+ torsion τ hτ (m*n) ρ where
  toFun x := ⟨x.val,by rw [mul_comm,mul_smul,x.property,zsmul_zero]⟩
  map_zero' := rfl
  map_add' _ _ := rfl
lemma into_injective : Function.Injective (into τ hτ m n ρ) := by
  intro x y h
  apply Subtype.ext
  exact congrArg Subtype.val h
lemma down_into (x : torsion τ hτ m ρ) : down τ hτ m n ρ (into τ hτ m n ρ x)=0 := by
  apply Subtype.ext
  exact x.property
/-- Exactness at the middle for ALL tests, without pointwise divisibility. -/
lemma kernel_iff (x : torsion τ hτ (m*n) ρ) :
    down τ hτ m n ρ x=0 ↔ ∃ y : torsion τ hτ m ρ,into τ hτ m n ρ y=x := by
  constructor
  · intro hx
    refine ⟨⟨x.val,congrArg Subtype.val hx⟩,?_⟩
    rfl
  · rintro ⟨y,rfl⟩
    exact down_into τ hτ m n ρ y
/-- The genuine universal kernel point, with its actual complex base. -/
@[expose] def universal (k : ℤ) : torsion τ hτ k (structureMap τ hτ k) :=
  ⟨⟨inclusion τ hτ k,rfl⟩,(torsion_iff τ hτ k _).mpr (equalizer.condition _ _)⟩
/-- Genuine whole scheme transition K_(mn) to K_n. -/
@[expose] def map : kernel τ hτ (m*n)⟶kernel τ hτ n :=
  ((pointsEquiv τ hτ n (structureMap τ hτ (m*n))).symm
    (down τ hτ m n _ (universal τ hτ (m*n)))).val
@[reassoc] lemma map_over : map τ hτ m n≫structureMap τ hτ n=structureMap τ hτ (m*n) :=
  ((pointsEquiv τ hτ n (structureMap τ hτ (m*n))).symm
    (down τ hτ m n _ (universal τ hτ (m*n)))).property
/-- The literal ambient multiplication square, not only closed-point action. -/
@[reassoc] lemma map_inclusion : map τ hτ m n≫inclusion τ hτ n=
    inclusion τ hτ (m*n)≫PELOriginalIntegerMultiplication318.multiplication τ hτ m := by
  have h := (pointsEquiv τ hτ n (structureMap τ hτ (m*n))).apply_symm_apply
    (down τ hτ m n _ (universal τ hτ (m*n)))
  have hh := congrArg (fun x => x.val.val) h
  change map τ hτ m n≫inclusion τ hτ n=
    (m • (universal τ hτ (m*n)).val).val at hh
  rw [PELOriginalIntegerMultiplication318.test_action τ hτ m
    (inclusion τ hτ (m*n)) (rfl : inclusion τ hτ (m*n)≫PELOriginalProductChartCover318.π τ hτ=structureMap τ hτ (m*n))]
  exact hh
end PELOriginalTorsionTowerPoints318
