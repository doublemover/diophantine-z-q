module
public import FramedZeroUniversalData318
public section
noncomputable section
namespace FramedZeroUniversalLift318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FramedZeroUniversalData318
universe u
variable {X T : Scheme.{u}} (D : Data X) (f : T ⟶ X) (hf : D.Vanishing f)
@[expose] def localMap (i : D.Index) : (D.testOpen f i).toScheme ⟶ D.Zero :=
  PrincipalZeroUniversal318.lift (D.equation i) (D.restriction f i)
    (by rw [D.restriction_equation,hf i,map_zero])≫D.chart i
@[reassoc] lemma localMap_inclusion (i : D.Index) :
    localMap D f hf i≫D.inclusion=(D.testOpen f i).ι≫f := by
  rw [localMap,Category.assoc,D.chart_inclusion,←Category.assoc,
    PrincipalZeroUniversal318.lift_inclusion,Scheme.Hom.resLE_comp_ι]
lemma compatible (i j : D.Index) :
    pullback.fst ((D.testCover f).f i) ((D.testCover f).f j)≫localMap D f hf i=
      pullback.snd ((D.testCover f).f i) ((D.testCover f).f j)≫localMap D f hf j := by
  apply (cancel_mono D.inclusion).1
  rw [Category.assoc,Category.assoc,localMap_inclusion,localMap_inclusion,←Category.assoc,
    ←Category.assoc,pullback.condition]

/-- Genuine global factorization obtained by scheme gluing on the full
pulled-back cover. Arbitrary nilpotents on T are retained throughout. -/
@[expose] def lift : T ⟶ D.Zero := (D.testCover f).glueMorphisms (localMap D f hf) (compatible D f hf)
@[reassoc] lemma chart_lift (i : D.Index) : (D.testOpen f i).ι≫lift D f hf=localMap D f hf i :=
  (D.testCover f).ι_glueMorphisms _ _ i
@[reassoc] lemma lift_inclusion : lift D f hf≫D.inclusion=f := by
  apply (D.testCover f).hom_ext
  intro i
  rw [←Category.assoc,chart_lift,localMap_inclusion]

/-- Conversely a factorization through the FULL zero scheme forces
vanishing in the entire pulled-back coefficient rings, not just residues. -/
lemma vanishing_of_factor (g : T ⟶ D.Zero) (hg : g≫D.inclusion=f) : D.Vanishing f := by
  intro i
  let q := (D.cartesian i).lift (D.restriction f i) ((D.testOpen f i).ι≫g) (by
    rw [Scheme.Hom.resLE_comp_ι,Category.assoc,hg])
  have hq : q≫D.localInclusion i=D.restriction f i := (D.cartesian i).lift_fst _ _ _
  have he : (D.restriction f i).appTop (D.equation i)=0 := by
    rw [←hq]
    change q.appTop ((D.localInclusion i).appTop (D.equation i))=0
    rw [PrincipalZeroUniversal318.inclusion_equation,map_zero]
  rw [D.restriction_equation] at he
  exact (LineFrameTopScalar318.ringTop (D.testOpen f i)).inv.injective (he.trans (map_zero _).symm)

/-- Actual unique representability of universal section vanishing. -/
theorem existsUnique_lift_iff :
    (∃! g : T ⟶ D.Zero,g≫D.inclusion=f) ↔ D.Vanishing f := by
  constructor
  · rintro ⟨g,hg,_⟩
    exact vanishing_of_factor D f g hg
  · intro h
    refine ⟨lift D f h,lift_inclusion D f h,?_⟩
    intro g hg
    apply (cancel_mono D.inclusion).1
    rw [lift_inclusion,hg]
end FramedZeroUniversalLift318
