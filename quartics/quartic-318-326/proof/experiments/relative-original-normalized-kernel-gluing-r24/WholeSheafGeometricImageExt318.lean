module
public import ContactOriginalIsomBaseChangedUniversal318
public import ContactDifferenceQuotientSheaf318
public section
noncomputable section
namespace WholeSheafGeometricImageExt318
open AlgebraicGeometry CategoryTheory Opposite
universe v u w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (F : Sheaf J (Type w)) {B X : C} (p : X ⟶ B)
/-- Equality on an actual geometric projection descends precisely when
its image sieve covers. No flatness or quotient representability is assumed. -/
lemma image_ext (hp : MorphismImageSieve318.image p ∈ J B)
    (x y : F.obj.obj (op B)) (h : F.obj.map p.op x=F.obj.map p.op y) : x=y := by
  have ht := (isSheaf_iff_isSheaf_of_type F.obj).mp F.property
  apply (ht.isSeparated _ hp).ext
  intro T f hf
  obtain ⟨g,rfl⟩ := hf
  change F.obj.map (p.op ≫ g.op) x=F.obj.map (p.op ≫ g.op) y
  rw [F.obj.map_comp]
  exact congrArg (F.obj.map g.op) h
end WholeSheafGeometricImageExt318
