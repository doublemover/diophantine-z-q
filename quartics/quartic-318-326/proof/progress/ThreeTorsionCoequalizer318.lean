module
public import ThreeTorsionOpenUniversal318
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public section
noncomputable section
namespace ThreeTorsionCoequalizer318
open CategoryTheory CategoryTheory.Limits NonverticalDoubling318 ThreeTorsionAlgebra318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

abbrev curveObject:=CommAlgCat.of R (Curve A B)
abbrev openObject:=CommAlgCat.of R (OpenRing A B)
abbrev torsionObject:=CommAlgCat.of R (Ring A B hD)
@[expose] def doubling : curveObject A B⟶openObject A B:=CommAlgCat.ofHom (double A B)
@[expose] def negation : curveObject A B⟶openObject A B:=CommAlgCat.ofHom (negative A B)
@[expose] def quotient : openObject A B⟶torsionObject A B hD:=CommAlgCat.ofHom (toTorsion A B hD)

lemma condition : doubling A B≫quotient A B hD=negation A B≫quotient A B hD:=by
  apply CommAlgCat.hom_ext
  exact NonverticalDoubling318.condition A B hD

@[expose] def cofork : Cofork (doubling A B) (negation A B):=
  Cofork.ofπ (quotient A B hD) (condition A B hD)

/-- The literal torsion algebra, with its actual localized coordinate map,
is the categorical coequalizer in commutative algebras over the original base. -/
@[expose] def isColimit : IsColimit (cofork A B hD):=by
  apply Cofork.IsColimit.ofExistsUnique
  intro s
  have hk:s.π.hom.comp (double A B)=s.π.hom.comp (negative A B):=
    congrArg CommAlgCat.Hom.hom s.condition
  obtain ⟨ψ,hψ,hunique⟩:=ThreeTorsionOpenUniversal318.existsUnique A B hD s.π.hom hk
  refine ⟨CommAlgCat.ofHom ψ,?_,?_⟩
  · exact CommAlgCat.hom_ext hψ
  · intro χ hχ
    apply CommAlgCat.hom_ext
    exact hunique χ.hom (congrArg CommAlgCat.Hom.hom hχ)

end ThreeTorsionCoequalizer318
