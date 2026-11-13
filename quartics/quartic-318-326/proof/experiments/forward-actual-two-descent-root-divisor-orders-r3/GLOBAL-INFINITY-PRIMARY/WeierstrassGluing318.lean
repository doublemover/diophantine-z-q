module
public import InfinitySmooth318
public import OpenJAffineScheme318
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace WeierstrassGluing318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeierstrassOverlap318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]

abbrev overlap (A B : R) : Scheme := Spec (CommRingCat.of (InfinityOverlap A B))

/-- The actual inclusion of the overlap into the Y=1 chart. -/
def intoInfinity (A B : R) : overlap A B ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom (algebraMap (Infinity A B) (InfinityOverlap A B)))
instance intoInfinity_open (A B : R) : IsOpenImmersion (intoInfinity A B) :=
  IsOpenImmersion.of_isLocalization (InfinityChart318.z A B)

/-- The actual overlap isomorphism, followed by the inclusion D(y) into the finite chart. -/
def intoAffine (A B : R) : overlap A B ⟶ ShortAffineScheme318.scheme A B :=
  Spec.map (overlapEquiv A B).toRingEquiv.toCommRingCatIso.inv ≫
    Spec.map (CommRingCat.ofHom (algebraMap (Affine A B) (AffineOverlap A B)))
instance intoAffine_open (A B : R) : IsOpenImmersion (intoAffine A B) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (Affine A B) (AffineOverlap A B)))) :=
    IsOpenImmersion.of_isLocalization (ShortAffineJacobian318.y A B)
  unfold intoAffine
  infer_instance

lemma intoAffine_eq (A B : R) : intoAffine A B=
    Spec.map (CommRingCat.ofHom (toInfinityBase A B).toRingHom) := by
  unfold intoAffine ShortAffineScheme318.scheme
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact toInfinity_map A B a

/-- Both chart inclusions have precisely the same map to the original base. -/
theorem overlap_over_base (A B : R) :
    intoAffine A B ≫ ShortAffineScheme318.structureMap A B=
      intoInfinity A B ≫ InfinitySmooth318.structureMap A B := by
  rw [intoAffine_eq]
  unfold ShortAffineScheme318.structureMap intoInfinity InfinitySmooth318.structureMap
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (toInfinityBase A B).commutes r

/-- The actual scheme glued from the two literal projective-cubic charts. -/
abbrev scheme (A B : R) : Scheme := pushout (intoAffine A B) (intoInfinity A B)

def finiteChart (A B : R) : ShortAffineScheme318.scheme A B ⟶ scheme A B :=
  pushout.inl _ _
def infinityChart (A B : R) : InfinitySmooth318.scheme A B ⟶ scheme A B :=
  pushout.inr _ _
instance finiteChart_open (A B : R) : IsOpenImmersion (finiteChart A B) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoAffine A B) (intoInfinity A B))
    WalkingSpan.left))
instance infinityChart_open (A B : R) : IsOpenImmersion (infinityChart A B) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span (intoAffine A B) (intoInfinity A B))
    WalkingSpan.right))

def structureMap (A B : R) : scheme A B ⟶ Spec (CommRingCat.of R) :=
  pushout.desc (ShortAffineScheme318.structureMap A B) (InfinitySmooth318.structureMap A B)
    (overlap_over_base A B)
@[simp] theorem finiteChart_structure (A B : R) :
    finiteChart A B ≫ structureMap A B=ShortAffineScheme318.structureMap A B :=
  pushout.inl_desc ..
@[simp] theorem infinityChart_structure (A B : R) :
    infinityChart A B ≫ structureMap A B=InfinitySmooth318.structureMap A B :=
  pushout.inr_desc ..

/-- The point at infinity is an actual section of the glued scheme. -/
def infinity (A B : R) : Spec (CommRingCat.of R) ⟶ scheme A B :=
  InfinitySmooth318.infinity A B ≫ infinityChart A B
@[simp] theorem infinity_section (A B : R) : infinity A B ≫ structureMap A B=𝟙 _ := by
  simp [infinity,Category.assoc,InfinitySmooth318.infinity_section]

/-- The two actual charts cover every point of the constructed scheme. -/
theorem charts_cover (A B : R) (p : scheme A B) :
    (∃ a,finiteChart A B a=p) ∨ (∃ b,infinityChart A B b=p) := by
  obtain ⟨i,q,hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoAffine A B) (intoInfinity A B)) p
  cases i with
  | none =>
    left
    refine ⟨intoAffine A B q,?_⟩
    change ((intoAffine A B) ≫ finiteChart A B) q=p
    rw [show intoAffine A B ≫ finiteChart A B=
      colimit.ι (span (intoAffine A B) (intoInfinity A B)) WalkingSpan.zero from colimit.w (span (intoAffine A B) (intoInfinity A B)) WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q,hq⟩
    | right => exact Or.inr ⟨q,hq⟩

/-- The actual glued structure morphism is smooth wherever the discriminant is a unit. -/
theorem structure_smooth (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    Smooth (structureMap A B) := by
  have hA := ShortAffineScheme318.structureMap_smooth A B hD
  have hI := InfinitySmooth318.structure_smooth A B hD
  apply IsZariskiLocalAtSource.of_openCover
    (Scheme.IsLocallyDirected.openCover (span (intoAffine A B) (intoInfinity A B)))
  intro i
  cases i with
  | none =>
    change Smooth (colimit.ι (span (intoAffine A B) (intoInfinity A B)) WalkingSpan.zero ≫ structureMap A B)
    rw [←colimit.w (span (intoAffine A B) (intoInfinity A B)) WalkingSpan.Hom.fst]
    change Smooth (intoAffine A B ≫ finiteChart A B ≫ structureMap A B)
    rw [finiteChart_structure]
    infer_instance
  | some j =>
    cases j with
    | left =>
      change Smooth (finiteChart A B ≫ structureMap A B)
      rw [finiteChart_structure]
      exact hA
    | right =>
      change Smooth (infinityChart A B ≫ structureMap A B)
      rw [infinityChart_structure]
      exact hI

/-- Literal family over the same open j-line base, with no extra smoothness premise. -/
abbrev literalScheme (N : ℕ) := scheme (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
abbrev literalStructureMap (N : ℕ) := structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
instance literal_smooth (N : ℕ) : Smooth (literalStructureMap N) :=
  structure_smooth _ _ (OpenJAffineScheme318.discriminant_unit N)
abbrev literalInfinity (N : ℕ) := infinity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
theorem literal_infinity_section (N : ℕ) : literalInfinity N ≫ literalStructureMap N=𝟙 _ :=
  infinity_section _ _

end WeierstrassGluing318
