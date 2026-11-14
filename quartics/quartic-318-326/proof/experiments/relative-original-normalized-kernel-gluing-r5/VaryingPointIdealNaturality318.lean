module
public import VaryingPointFamilyBaseChange318
public import VaryingFreeParameterPoints318
public import AffineClosedIdealBaseChange318
public section
noncomputable section
namespace VaryingPointIdealNaturality318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
lemma ideal_map (x : VaryingParameterPoint318.Point R A ι S) :
    VaryingParameterPointIdeal318.ideal R A ι T (VaryingParameterPoint318.map R A ι S T f x)=
      Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom
        (VaryingParameterPointIdeal318.ideal R A ι S x) :=
  AffineClosedIdealBaseChange318.ideal_map (S ⊗[R] A) (T ⊗[R] A)
    (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom
    (VaryingParameterPointFamily318.intoSource R A ι S x)
    (VaryingParameterPointFamily318.intoSource R A ι T (VaryingParameterPoint318.map R A ι S T f x))
    (VaryingPointFamilyBaseChange318.map R A ι S x T f)
    (VaryingPointFamilyBaseChange318.source_cartesian R A ι S x T f)
@[expose] def mapFree (x : VaryingFreeParameterPoints318.FreePoint R A ι S) :
    VaryingFreeParameterPoints318.FreePoint R A ι T :=
  ⟨VaryingParameterPoint318.map R A ι S T f x.val,by
    rw [ideal_map]
    have h := (VaryingFreeIdealClassifyingMap318.mapIdeal R A ι S T f
      (VaryingFreeParameterPoints318.recover R A ι S x)).property
    rw [VaryingFreeIdealClassifyingMap318.mapIdeal_val] at h
    exact h⟩
lemma recover_natural (x : VaryingFreeParameterPoints318.FreePoint R A ι S) :
    VaryingFreeParameterPoints318.recover R A ι T (mapFree R A ι S T f x)=
      VaryingFreeIdealClassifyingMap318.mapIdeal R A ι S T f
        (VaryingFreeParameterPoints318.recover R A ι S x) := by
  apply Subtype.ext
  exact (ideal_map R A ι S T f x.val).trans
    (VaryingFreeIdealClassifyingMap318.mapIdeal_val R A ι S T f
      (VaryingFreeParameterPoints318.recover R A ι S x)).symm
lemma classify_natural (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S) :
    mapFree R A ι S T f (VaryingFreeParameterPoints318.classify R A ι S I)=
      VaryingFreeParameterPoints318.classify R A ι T
        (VaryingFreeIdealClassifyingMap318.mapIdeal R A ι S T f I) := by
  apply Subtype.ext
  exact VaryingParameterPoint318.map_ofIdeal R A ι S T f I
end VaryingPointIdealNaturality318
