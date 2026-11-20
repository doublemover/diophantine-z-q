module
public import SelectedCompletedMultiplication318
public import CompletedAdditionCoefficient318
public import ZeroFiberBaseChange318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318
open SelectedCompletedMultiplication318 WeierstrassCoefficientMap318

namespace SelectedMultiplicationCoefficient318
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (A B : R) (h : IsUnit (-16*(4*A^3+27*B^2)))
local notation "a" => algebraMap R S
local notation "p" => structureMap A B
local notation "p₁" => structureMap (a A) (a B)
local notation "f" => coefficientMap (S:=S) A B
local notation "b" => Spec.map (CommRingCat.ofHom a)
local notation "h₁" => CompletedAdditionCoefficient318.mapped_discriminant (S:=S) A B h
local notation "P" => CompletedCoefficientProduct318.pair (S:=S) A B

/-- Actual arbitrary natural multiplication commutes with the actual
coefficient morphism R→S. The two induction legs are the relative
product projections, not equality merely on field-valued points. -/
theorem naturality (m : ℕ) :
    f ≫ mul A B h m = mul (a A) (a B) h₁ m ≫ f := by
  induction m with
  | zero =>
      calc
        _ = p₁ ≫ (b ≫ infinity A B) := by
          rw [mul_zero,←Category.assoc,coefficientMap_base,Category.assoc]
        _ = _ := by
          rw [mul_zero,Category.assoc p₁ (infinity (a A) (a B)) f,coefficientMap_infinity]
  | succ k ih =>
      have he : f ≫ stepPair A B (iterate A B h k) =
          stepPair (a A) (a B) (iterate (a A) (a B) h₁ k) ≫ P := by
        apply pullback.hom_ext
        · simp only [Category.assoc,stepPair_fst,CompletedCoefficientProduct318.pair_fst,
            stepPair_fst_assoc]
          exact ih
        · simp only [Category.assoc,stepPair_snd,CompletedCoefficientProduct318.pair_snd,
            stepPair_snd_assoc,Category.id_comp,Category.comp_id]
      rw [mul_succ,mul_succ,←Category.assoc,he,Category.assoc,
        CompletedAdditionCoefficient318.addition A B h h₁,←Category.assoc]

/-- The zero-fiber data use the true completed base-change model and the
actual two [m] morphisms. Both square conditions are now proved. -/
@[expose] def kernelData (m : ℕ) :
    ZeroFiberBaseChange318.Data (scheme A B) (scheme (a A) (a B))
      (Spec (CommRingCat.of R)) (Spec (CommRingCat.of S)) where
  p := p
  p' := p₁
  f := f
  b := b
  cartesian := WeierstrassBaseChange318.coefficient_base_pullback A B
  t := mul A B h m
  t' := mul (a A) (a B) h₁ m
  e := infinity A B
  e' := infinity (a A) (a B)
  t_base := mul_base A B h m
  t'_base := mul_base (a A) (a B) h₁ m
  e_base := infinity_section A B
  e'_base := infinity_section (a A) (a B)
  commute := naturality A B h m
  section_map := coefficientMap_infinity A B

abbrev K₀ (m : ℕ) := pullback (mul A B h m) (infinity A B)
abbrev K₁ (m : ℕ) := pullback (mul (a A) (a B) h₁ m) (infinity (a A) (a B))

@[expose] def kernelMap (m : ℕ) : K₁ (S:=S) A B h m ⟶ K₀ A B h m :=
  ZeroFiberBaseChange318.map (kernelData A B h m)

@[reassoc] theorem kernelMap_curve (m : ℕ) :
    kernelMap (S:=S) A B h m ≫ pullback.fst (mul A B h m) (infinity A B) =
      pullback.fst (mul (a A) (a B) h₁ m) (infinity (a A) (a B)) ≫ f :=
  ZeroFiberBaseChange318.map_fst (kernelData A B h m)

@[reassoc] theorem kernelMap_base (m : ℕ) :
    kernelMap (S:=S) A B h m ≫ pullback.snd (mul A B h m) (infinity A B) =
      pullback.snd (mul (a A) (a B) h₁ m) (infinity (a A) (a B)) ≫ b :=
  ZeroFiberBaseChange318.map_snd (kernelData A B h m)

/-- The actual [m] zero fiber, not just the marked point set, is the
base change of the original zero fiber. -/
theorem kernel_pullback (m : ℕ) : IsPullback (kernelMap (S:=S) A B h m)
    (pullback.snd (mul (a A) (a B) h₁ m) (infinity (a A) (a B)))
    (pullback.snd (mul A B h m) (infinity A B)) b :=
  ZeroFiberBaseChange318.isPullback (kernelData A B h m)

end SelectedMultiplicationCoefficient318

#print axioms SelectedMultiplicationCoefficient318.naturality
#print axioms SelectedMultiplicationCoefficient318.kernel_pullback
