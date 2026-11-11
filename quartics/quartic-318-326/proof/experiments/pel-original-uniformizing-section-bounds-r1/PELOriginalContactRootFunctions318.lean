module
public import PELOriginalGenericContactRoots318
public import PELOriginalContactBranchSquare318
public section
noncomputable section
namespace PELOriginalContactRootFunctions318
open Set
open scoped OnePoint
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactBranchSquare318 FourCharacterRootRecombination318

/-- The unchanged original full-source regular locus excludes precisely
the full branch image. It does not select components or label points. -/
@[expose] def RegularSource : Set UnlevelledBase:=
  {x|PELOriginalMaximalQuotient318.projection x∉PELStabilizerLocusInvariant318.branchImage}
@[expose] def base (x:UnlevelledBase):ℂ:=ComplexSphereCharts318.affine (normalizedMap x)
@[expose] def roots (x:UnlevelledBase) (k:Fin 4):ℂ:=
  triple (fun i=>PELOriginalCommonCubicCoordinate318.ordinate i
    (PELOriginalCharacterQuotient318.toCharacter i x)) k/denominator branches (base x)

lemma normalized_finite (x:UnlevelledBase) (hx:x∈RegularSource) :
    normalizedMap x=(base x:OnePoint ℂ) := by
  have hn:normalizedMap x≠∞:=by
    intro he
    have hh:PELOriginalMaximalQuotient318.projection x=
        PELOriginalMarkedSphere318.branchPoint 4:=
      PELOriginalManuscriptNormalization318.coordinate.injective
        (he.trans PELOriginalManuscriptNormalization318.value210.symm)
    apply hx
    rw [hh]
    exact (PELOriginalFiniteRamification318.displayed 4).property
  obtain ⟨t,ht⟩:=OnePoint.ne_infty_iff_exists.mp hn
  have hb:base x=t:=by
    change ComplexSphereCharts318.affine (normalizedMap x)=t
    rw [←ht,ComplexSphereCharts318.affine_coe]
  rw [hb]
  exact ht.symm

lemma original_base (x:UnlevelledBase) (hx:x∈RegularSource) :
    PELOriginalMaximalQuotient318.projection x=basePoint (base x) := by
  apply PELOriginalManuscriptNormalization318.coordinate.injective
  exact (normalized_finite x hx).trans (basePoint_value _).symm

lemma denominator_ne (x:UnlevelledBase) (hx:x∈RegularSource) :
    denominator branches (base x)≠0:=
  (PELOriginalCommonContactBase318.regular_iff _).mp ((original_base x hx) ▸ hx)

lemma base_at (t:ℂ) (x:UnlevelledBase)
    (hx:PELOriginalMaximalQuotient318.projection x=basePoint t) : base x=t:=by
  change ComplexSphereCharts318.affine
    (PELOriginalManuscriptNormalization318.coordinate (PELOriginalMaximalQuotient318.projection x))=t
  rw [hx,basePoint_value,ComplexSphereCharts318.affine_coe]

lemma roots_fiber (t:ℂ) (hD:denominator branches t≠0)
    (x:PELOriginalRegularCharacterProduct318.SourceFiber (basePoint t)) (k:Fin 4) :
    roots x.val k=(PELOriginalGenericContactRoots318.rootsEquiv t hD x).val k:=by
  rw [PELOriginalGenericContactRoots318.roots_formula]
  change _/denominator branches (base x.val)=_
  rw [base_at t x.val x.property]

/-- The actual global functions satisfy all four linear root equations
on the full original regular locus. Their explicit formula, not an
independent choice per fiber, is what analytic extension consumes. -/
theorem roots_square (x:UnlevelledBase) (hx:x∈RegularSource) (k:Fin 4) :
    roots x k^2=base x-branches k:=by
  let xf:PELOriginalRegularCharacterProduct318.SourceFiber (basePoint (base x)):=
    ⟨x,original_base x hx⟩
  rw [show roots x k= (PELOriginalGenericContactRoots318.rootsEquiv (base x)
      (denominator_ne x hx) xf).val k from roots_fiber _ _ xf k]
  exact PELOriginalGenericContactRoots318.roots_square _ _ xf k

/-- The global functions separate actual original points, including
points lying on different generic fibers. -/
theorem base_roots_injective (x y:UnlevelledBase) (hx:x∈RegularSource) (hy:y∈RegularSource)
    (ht:base x=base y) (hr:∀k,roots x k=roots y k) : x=y := by
  let xf:PELOriginalRegularCharacterProduct318.SourceFiber (basePoint (base x)):=
    ⟨x,original_base x hx⟩
  let yf:PELOriginalRegularCharacterProduct318.SourceFiber (basePoint (base x)):=
    ⟨y,(original_base y hy).trans (congrArg basePoint ht.symm)⟩
  have h:PELOriginalGenericContactRoots318.rootsEquiv (base x) (denominator_ne x hx) xf=
      PELOriginalGenericContactRoots318.rootsEquiv (base x) (denominator_ne x hx) yf:=by
    apply Subtype.ext
    funext k
    rw [←roots_fiber _ _ xf k,←roots_fiber _ _ yf k]
    exact hr k
  exact congrArg Subtype.val ((PELOriginalGenericContactRoots318.rootsEquiv _ _).injective h)

/-- Every tuple on every genuinely generic finite base is realized by
one and only one point of the original genus-five source. -/
theorem all_roots (t:ℂ) (hD:denominator branches t≠0)
    (z:Fin 4→ℂ) (hz:∀k,z k^2=t-branches k) :
    ∃x:UnlevelledBase,x∈RegularSource ∧ base x=t ∧ ∀k,roots x k=z k := by
  obtain ⟨x,hx,hunique⟩:=PELOriginalGenericContactRoots318.all_actual_roots t hD z hz
  refine ⟨x.val,?_,base_at t x.val x.property,?_⟩
  · change PELOriginalMaximalQuotient318.projection x.val∉_
    rw [x.property]
    exact (PELOriginalCommonContactBase318.regular_iff t).mpr hD
  · intro k
    rw [roots_fiber t hD x k]
    exact hx k
end PELOriginalContactRootFunctions318
