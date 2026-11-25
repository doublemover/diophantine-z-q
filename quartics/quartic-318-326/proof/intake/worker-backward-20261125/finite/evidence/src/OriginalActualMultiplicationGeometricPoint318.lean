module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section
noncomputable section

namespace OriginalActualMultiplicationGeometricPoint318

open AlgebraicGeometry CategoryTheory Limits

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
local notation "K" => CommRingCat.of k
local notation "Sk" => Spec K

/-- Construct a real field-point on a nonempty actual finite-type
scheme over an algebraically closed field. This is weaker than
Nullstellensatz for all equations: choose one genuine affine open,
a maximal residue field and use Zariski's lemma. -/
theorem exists_field_point {X : Scheme.{u}} (f : X ⟶ Sk)
    [LocallyOfFiniteType f] (x : X) :
    ∃ e : Sk ⟶ X, e≫f=𝟙 Sk := by
  obtain ⟨R,j,openJ,⟨r,_⟩,_⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (U:=⊤) (show x∈(⊤ : X.Opens) from Set.mem_univ _)
  letI : IsOpenImmersion j := openJ
  let g : Spec R ⟶ Sk := j≫f
  let u : K ⟶ R := Spec.preimage g
  have u_eq : Spec.map u=g := Spec.map_preimage g
  have ft : u.hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType) u).1
    rw [u_eq]
    change LocallyOfFiniteType (j≫f)
    infer_instance
  have nz : (1:R)≠0 := by
    intro h
    exact r.asIdeal.isPrime.ne_top (Ideal.eq_top_iff_one.2 (h.symm ▸ r.asIdeal.zero_mem))
  letI : Nontrivial R := nontrivial_of_ne 1 0 nz
  letI : Algebra k R := u.hom.toAlgebra
  letI : Algebra.FiniteType k R := ft
  obtain ⟨M,hM⟩ := Ideal.exists_maximal R
  letI : M.IsMaximal := hM
  let L := R ⧸ M
  letI : Field L := Ideal.Quotient.field M
  letI : Algebra.FiniteType k L := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k M)
    (Ideal.Quotient.mkₐ_surjective k M)
  letI : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  let e : k ≃ₐ[k] L := AlgEquiv.ofBijective (Algebra.ofId k L)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=k))
  let v : R ⟶ K := CommRingCat.ofHom (e.symm.toRingHom.comp (Ideal.Quotient.mk M))
  have vu : u≫v=𝟙 K := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change e.symm (Ideal.Quotient.mk M (algebraMap k R c))=c
    rw [←IsScalarTower.algebraMap_apply k R L]
    exact e.symm.commutes c
  refine ⟨Spec.map v≫j,?_⟩
  rw [Category.assoc]
  change Spec.map v≫g=𝟙 Sk
  rw [←u_eq,←Spec.map_comp,vu,Spec.map_id]

/-- Scheme surjectivity of the actual multiplication gives
surjectivity on its actual geometric points by using the literal
scheme-theoretic fibre at each point. -/
theorem lift_actual_geometric_point {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Surjective f] (p : Sk ⟶ Y) :
    ∃ z : Sk ⟶ X, z≫f=p := by
  let g := pullback.snd f p
  have x : Nonempty (pullback f p) := by
    let t : Sk := (⊥ : PrimeSpectrum k)
    obtain ⟨u,_⟩ := g.surjective t
    exact ⟨u⟩
  obtain ⟨e,he⟩ := exists_field_point g (Classical.choice x)
  refine ⟨e≫pullback.fst f p,?_⟩
  rw [Category.assoc,pullback.condition,←Category.assoc,he,Category.id_comp]

end OriginalActualMultiplicationGeometricPoint318
