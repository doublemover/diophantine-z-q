module
public import ContactBoundedHilbertEquiv318
public section
noncomputable section
namespace ContactBoundedHilbertNaturality318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B T : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (g : T ⟶ B) (hg : g ≫ b=t)
@[expose] def pointMap (f : ContactBoundedPointFamily318.SchemePoint c N b) : ContactBoundedPointFamily318.SchemePoint c N t :=
  ⟨g ≫ f.val,by rw [Category.assoc,f.property]; exact hg⟩
lemma extract_natural (f : ContactBoundedPointFamily318.SchemePoint c N b) :
    ContactBoundedHilbertBaseChange318.map c N b t g hg (ContactBoundedPointFamily318.extract c N b f)=
      ContactBoundedPointFamily318.extract c N t (pointMap c N b t g hg f) := by
  apply ContactBoundedSchemeHilbertData318.Data.ext
  have hb := ClosedPullbackKernel318.ideal _ _ _ _ (ContactBoundedPointFamily318.cartesian c N b f)
  have ht := ClosedPullbackKernel318.ideal _ _ _ _ (ContactBoundedPointFamily318.cartesian c N t (pointMap c N b t g hg f))
  change (ContactBoundedPointFamily318.into c N b f).ker.comap
    (ContactBoundedHilbertBaseChange318.sourceMap c b t g hg)=_
  rw [hb,← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,RelativeSchemeCoefficient318.comp]
  exact ht.symm
/-- Bounded classification is natural under EVERY coefficient scheme
morphism for the literal whole ideal-comap action, even when ranks vary. -/
lemma natural (D : ContactBoundedSchemeHilbertData318.Data c N b) :
    ContactBoundedHilbertEquiv318.equivalence c N t (ContactBoundedHilbertBaseChange318.map c N b t g hg D)=
      pointMap c N b t g hg (ContactBoundedHilbertEquiv318.equivalence c N b D) := by
  apply (ContactBoundedHilbertEquiv318.equivalence c N t).symm.injective
  rw [Equiv.symm_apply_apply]
  change ContactBoundedHilbertBaseChange318.map c N b t g hg D=
    ContactBoundedPointFamily318.extract c N t (pointMap c N b t g hg (ContactBoundedHilbertEquiv318.equivalence c N b D))
  rw [← extract_natural]
  exact congrArg (ContactBoundedHilbertBaseChange318.map c N b t g hg)
    ((ContactBoundedHilbertEquiv318.equivalence c N b).symm_apply_apply D).symm
end ContactBoundedHilbertNaturality318
