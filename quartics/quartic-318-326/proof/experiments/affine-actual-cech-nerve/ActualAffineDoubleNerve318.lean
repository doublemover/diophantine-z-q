module
public import ActualOverlapDiagram318
public import AffineCechRings318
public section
noncomputable section
namespace ActualAffineDoubleNerve318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AffineModuleBaseChange318
open AffineCechRings318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]
abbrev baseMap := Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The original categorical double fiber product has exactly the original
double tensor spectrum, through Mathlib's actual limit comparison. -/
@[expose] def doubleIso : ActualOverlapDiagram318.Double (baseMap R S) ≅ Spec (double R S) :=
  pullbackSpecIso R S S

@[reassoc] lemma inverse_first : (doubleIso R S).inv ≫
    ActualOverlapDiagram318.first (baseMap R S) = Spec.map (leftMap R S S) :=
  pullbackSpecIso_inv_fst' R S S
@[reassoc] lemma inverse_second : (doubleIso R S).inv ≫
    ActualOverlapDiagram318.second (baseMap R S) = Spec.map (rightMap R S S) :=
  pullbackSpecIso_inv_snd R S S
@[reassoc] lemma forward_first : (doubleIso R S).hom ≫ Spec.map (leftMap R S S) =
    ActualOverlapDiagram318.first (baseMap R S) := pullbackSpecIso_hom_fst' R S S
@[reassoc] lemma forward_second : (doubleIso R S).hom ≫ Spec.map (rightMap R S S) =
    ActualOverlapDiagram318.second (baseMap R S) := pullbackSpecIso_hom_snd R S S
@[reassoc] lemma forward_base : (doubleIso R S).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (double R S))) =
      ActualOverlapDiagram318.first (baseMap R S) ≫ baseMap R S :=
  pullbackSpecIso_hom_base R S S

/-- The actual categorical diagonal is the exact tensor multiplication
spectrum map followed by the same actual double comparison. -/
lemma diagonal : ActualOverlapDiagram318.diagonal (baseMap R S) =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R :
      S ⊗[R] S →ₐ[R] S).toRingHom) ≫ (doubleIso R S).inv :=
  diagonal_SpecMap R S

lemma spec_path {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (hh : g.hom.comp f.hom = h.hom) : Spec.map g ≫ Spec.map f = Spec.map h := by
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact congrArg (fun k : A →+* C => k a) hh
end ActualAffineDoubleNerve318
