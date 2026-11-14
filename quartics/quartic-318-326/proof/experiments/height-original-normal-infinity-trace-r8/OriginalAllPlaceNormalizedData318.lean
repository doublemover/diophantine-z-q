module
public import OriginalPointFinitePlaceRoots318
public import NormalizedOriginalValuativeCenter318
public import NormalizedWholeProjectiveProper318
public section
noncomputable section
namespace OriginalAllPlaceNormalizedData318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))

/-- Original rational twists in the SAME point field. No unit condition in
its valuation integer ring is asserted or needed. -/
@[expose] def fieldTwists (i : Fin 4) : (K c t)ˣ :=
  Units.map (algebraMap ℚ (K c t)) (c i)

theorem original_root_equations (i : Fin 4) :
    (roots c t i)^2 = (fieldTwists c t i : K c t) *
      ((t : K c t) - algebraMap (V c t w) (K c t)
        (IntegralSourceBranches318.contacts (V c t w) i)) := by
  have hc : algebraMap (V c t w) (K c t)
      (IntegralSourceBranches318.contacts (V c t w) i) =
        (LinearContactSquareclass318.contacts i : K c t) := by
    fin_cases i <;> norm_num [IntegralSourceBranches318.contacts,
      LinearContactSquareclass318.contacts]
  rw [hc]
  change (roots c t i)^2 = algebraMap ℚ (K c t) (c i : ℚ) * _
  rw [map_ratCast]
  have h := roots_square c t i
  push_cast at h
  exact h

/-- Constructed data at EVERY actual finite place, including all primes
excluded by the good model. The model is the whole normalized order model;
this structure intentionally contains no assertion that it is regular. -/
structure Data where
  pi : V c t w
  irreducible : Irreducible pi
  unit : Fin 4 → (V c t w)ˣ
  exponent : Fin 4 → Fin 2
  multiplier : Fin 4 → K c t
  multiplier_ne : ∀ i, multiplier i ≠ 0
  original_coefficient : ∀ i, (fieldTwists c t i : K c t) =
    algebraMap (V c t w) (K c t)
      ((unit i : V c t w) * pi^(exponent i : ℕ)) * (multiplier i)^2

namespace Data
variable (D : Data c t w)
@[expose] def coefficients : Fin 4 → V c t w :=
  fun i => (D.unit i : V c t w) * D.pi^(D.exponent i : ℕ)
@[expose] def normalizedRoots : Fin 4 → K c t :=
  fun i => roots c t i / D.multiplier i

theorem root_equation (i : Fin 4) : (D.normalizedRoots i)^2 =
    algebraMap (V c t w) (K c t) (D.coefficients i) *
      ((t : K c t) - algebraMap (V c t w) (K c t)
        (IntegralSourceBranches318.contacts (V c t w) i)) :=
  DVRNormalizedContactPoint318.root_relation _ _ _ _ _ _
    (D.multiplier_ne i) (D.original_coefficient i) (original_root_equations c t w i)

theorem original_signed_root (i : Fin 4) :
    D.multiplier i * D.normalizedRoots i = RationalContactPoint318.sourcePoint c t
      (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i) := by
  rw [←roots_original]
  exact DVRNormalizedContactPoint318.original_root _ _ (D.multiplier_ne i)

@[expose] def model : Scheme := NormalizedWholeGluing318.scheme (V c t w)
  D.coefficients (IntegralSourceBranches318.contacts (V c t w))
@[expose] def structureMap : D.model ⟶ Spec (CommRingCat.of (V c t w)) :=
  NormalizedWholeProjection318.structureMap (V c t w) D.coefficients
    (IntegralSourceBranches318.contacts (V c t w))
@[expose] def genericPoint : Spec (CommRingCat.of (K c t)) ⟶ D.model :=
  NormalizedGenericPointExtension318.point (V c t w) (K c t) D.coefficients
    (IntegralSourceBranches318.contacts (V c t w)) (t : K c t)
    D.normalizedRoots D.root_equation

theorem proper_separated : IsProper D.structureMap ∧ IsSeparated D.structureMap :=
  NormalizedWholeProjectiveProper318.proper_separated _ _ _
end Data

/-- No original-point, chosen uniformizer, unit-twist, coordinate-integrality
or good-place premise is requested. Both full-map generic specialization and
the exact original valuation-base section are produced. -/
theorem exists_center : ∃ (D : Data c t w)
    (g : Spec (CommRingCat.of (V c t w)) ⟶ D.model),
    g ≫ D.structureMap = 𝟙 _ ∧
    Spec.map (CommRingCat.ofHom (algebraMap (V c t w) (K c t))) ≫ g = D.genericPoint := by
  obtain ⟨pi,hpi⟩ := IsDiscreteValuationRing.exists_irreducible (V c t w)
  obtain ⟨u,e,s,hs,hc,g,hbase,hgeneric⟩ :=
    NormalizedOriginalValuativeCenter318.exists_center (V c t w) (K c t) pi hpi
      (fieldTwists c t) (IntegralSourceBranches318.contacts (V c t w))
      (t : K c t) (roots c t) (original_root_equations c t w)
  let D : Data c t w := ⟨pi,hpi,u,e,s,hs,hc⟩
  exact ⟨D,g,hbase,hgeneric⟩
end OriginalAllPlaceNormalizedData318
