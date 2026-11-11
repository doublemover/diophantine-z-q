module
public import OriginalCoefficientCohomology318
public section
noncomputable section
namespace OriginalCoefficientCohomologyMaps318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open NonreducedLineRestriction318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) {X : Scheme.{0}} (p : X ⟶ Spec R)
  (L N : Line X) (a : L.object ⟶ N.object)
@[expose] def additiveMap : additive L ⟶ additive N :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map a

lemma coefficient_square (r : R) :
    OriginalCoefficientCohomology318.multiply R p L r ≫ additiveMap L N a =
      additiveMap L N a ≫ OriginalCoefficientCohomology318.multiply R p N r := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change a.app U.unop ((OriginalCoefficientCohomology318.multiply R p L r).hom.app U s) =
    (OriginalCoefficientCohomology318.multiply R p N r).hom.app U (a.app U.unop s)
  rw [OriginalCoefficientCohomology318.multiply_apply,OriginalCoefficientCohomology318.multiply_apply]
  exact Scheme.Modules.Hom.app_smul a _ _

variable (n : ℕ)
local instance : Module R (Sheaf.H (additive L) n) :=
  OriginalCoefficientCohomology318.cohomologyModule R p L n
local instance : Module R (Sheaf.H (additive N) n) :=
  OriginalCoefficientCohomology318.cohomologyModule R p N n

/-- The actual derived cohomology map is linear for original structural
coefficients. This does not define a new map through a Cech quotient. -/
@[expose] def map : Sheaf.H (additive L) n →ₗ[R] Sheaf.H (additive N) n where
  __ := Sheaf.H.map (additiveMap L N a) n
  map_smul' r x := by
    change Sheaf.H.map (additiveMap L N a) n
      (Sheaf.H.map (OriginalCoefficientCohomology318.multiply R p L r) n x) =
      Sheaf.H.map (OriginalCoefficientCohomology318.multiply R p N r) n
        (Sheaf.H.map (additiveMap L N a) n x)
    rw [← Sheaf.H.map_comp_apply,← Sheaf.H.map_comp_apply,coefficient_square]

/-- Original sheaf isomorphisms induce actual structural-linear Hn
isomorphisms, for later coefficient identity/composition comparisons. -/
@[expose] def equivalence (e : L.object ≅ N.object) :
    Sheaf.H (additive L) n ≃ₗ[R] Sheaf.H (additive N) n where
  __ := map R p L N e.hom n
  invFun := map R p N L e.inv n
  left_inv x := by
    change Sheaf.H.map (additiveMap N L e.inv) n (Sheaf.H.map (additiveMap L N e.hom) n x) = x
    rw [← Sheaf.H.map_comp_apply]
    have h : additiveMap L N e.hom ≫ additiveMap N L e.inv = 𝟙 _ := by
      rw [additiveMap,additiveMap,← Functor.map_comp,e.hom_inv_id,Functor.map_id]
    rw [h,Sheaf.H.map_id_apply]
  right_inv x := by
    change Sheaf.H.map (additiveMap L N e.hom) n (Sheaf.H.map (additiveMap N L e.inv) n x) = x
    rw [← Sheaf.H.map_comp_apply]
    have h : additiveMap N L e.inv ≫ additiveMap L N e.hom = 𝟙 _ := by
      rw [additiveMap,additiveMap,← Functor.map_comp,e.inv_hom_id,Functor.map_id]
    rw [h,Sheaf.H.map_id_apply]
end OriginalCoefficientCohomologyMaps318
