module
public import SelectedTwistExactOrder318
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial EvenContactEtale318
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedSignedMultiplication318

namespace SelectedTwistGeometricOrder318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
variable (hY : IsUnit (ybar n I))
local notation "d" => twistUnit n I τ hτ hY
local notation "P" => SelectedTwistMarkOverCover318.twistPoint n I τ hτ hY

/-- Every actual geometric point of the fixed base lifts through the
specific ordinate-root cover. The root is selected in the field of
the given geometric test, not by changing the fixed-base map. -/
theorem geometric_lift (K : Type) [Field K] [IsAlgClosed K] [Algebra F K] :
    Nonempty (Q →ₐ[F] K) := by
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F K (d:F)) (by decide : 0 < 2)
  let v : RootRing d →ₐ[F] K := AdjoinRoot.liftAlgHom (polynomial d) (Algebra.ofId F K) u (by
    simpa only [polynomial,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,Algebra.ofId_apply] using
      sub_eq_zero.mpr hu)
  exact ⟨v.comp (SelectedOrdinateTorsor318.rootIso n I τ hτ hY).symm.toAlgHom⟩

variable (m : ℕ) [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]
variable (hm : 1 < m)
variable (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of Q))
variable (he : intoAffine n m hm =
  e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

include he in
/-- The canonical twist section has exact order m at EVERY geometric
point of its true fixed base. Each lifted point is evaluated on the
same original literal primitive scheme. -/
theorem exact_geometric {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F)) :
    ExactTests (disc_unit n I τ hτ hY) m (t ≫ P) := by
  obtain ⟨b,hb⟩ := Spec.map_surjective t
  letI : Algebra F K := b.hom.toAlgebra
  obtain ⟨p⟩ := geometric_lift n I τ hτ hY K
  let z : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of Q) :=
    Spec.map (CommRingCat.ofHom p.toRingHom)
  have hbase : z ≫ Spec.algebraMap F Q = t := by
    rw [←hb]
    change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F Q)) = Spec.map b
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact p.commutes a
  have h := SelectedTwistExactOrder318.exact_on_field_of_cover n I τ hτ hY m hm e he z
  rw [←Category.assoc,hbase] at h
  exact h

end SelectedTwistGeometricOrder318

#print axioms SelectedTwistGeometricOrder318.geometric_lift
#print axioms SelectedTwistGeometricOrder318.exact_geometric
