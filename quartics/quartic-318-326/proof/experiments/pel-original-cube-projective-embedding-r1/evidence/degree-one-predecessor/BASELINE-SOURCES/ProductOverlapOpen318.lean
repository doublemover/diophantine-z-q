module
public import ProductLocalization318
public import CanonicalRestrictionComparison318
public section
noncomputable section
namespace ProductOverlapOpen318
open AlgebraicGeometry CategoryTheory ProductLocalization318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {S : Type*} [CommRing S]

abbrev Iterated (x y : S) := Localization.Away (algebraMap S (Localization.Away x) y)

/-- The actual double localization and actual product localization are equivalent
    over the original coordinate ring. -/
@[expose] def productEquiv (x y : S) : Common x y ≃ₐ[S] Iterated x y :=
  IsLocalization.algEquiv (Submonoid.powers (x*y)) _ _

/-- The equivalence intertwines the actual previously constructed overlap map. -/
theorem productEquiv_leftMap (x y : S) (a : Localization.Away x) :
    productEquiv x y (leftMap (R:=S) x y a)=
      algebraMap (Localization.Away x) (Iterated x y) a := by
  have h : (productEquiv x y).toAlgHom.comp (leftMap (R:=S) x y)=
      Algebra.algHom S (Localization.Away x) (Iterated x y) := by
    apply IsLocalization.algHom_ext (Submonoid.powers x)
    ext
  exact AlgHom.congr_fun h a

/-- The actual overlap map is itself a principal localization, not merely a map
    between rings abstractly isomorphic to localizations. -/
theorem left_isLocalization (x y : S) :
    letI : Algebra (Localization.Away x) (Common x y) := (leftMap (R:=S) x y).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap S (Localization.Away x) y) (Common x y) := by
  letI : Algebra (Localization.Away x) (Common x y) := (leftMap (R:=S) x y).toRingHom.toAlgebra
  let e : Common x y ≃ₐ[Localization.Away x] Iterated x y :=
    { (productEquiv x y).toRingEquiv with
      commutes' := productEquiv_leftMap x y }
  exact IsLocalization.isLocalization_of_algEquiv _ e.symm

/-- The actual overlap scheme map is an open immersion. -/
theorem left_spec_open (x y : S) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (leftMap (R:=S) x y).toRingHom)) := by
  letI : Algebra (Localization.Away x) (Common x y) := (leftMap (R:=S) x y).toRingHom.toAlgebra
  letI := left_isLocalization x y
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (Localization.Away x) (Common x y))))
  exact IsOpenImmersion.of_isLocalization (algebraMap S (Localization.Away x) y)

/-- The same actual overlap ring map is formally étale. -/
theorem left_formallyEtale (x y : S) :
    letI : Algebra (Localization.Away x) (Common x y) := (leftMap (R:=S) x y).toRingHom.toAlgebra
    Algebra.FormallyEtale (Localization.Away x) (Common x y) := by
  letI : Algebra (Localization.Away x) (Common x y) := (leftMap (R:=S) x y).toRingHom.toAlgebra
  letI := left_isLocalization x y
  exact Algebra.FormallyEtale.of_isLocalization
    (Submonoid.powers (algebraMap S (Localization.Away x) y))


@[expose] def productEquivRight (x y : S) : Common x y ≃ₐ[S] Iterated y x :=
  IsLocalization.algEquiv (Submonoid.powers (x*y)) _ _

theorem productEquiv_rightMap (x y : S) (a : Localization.Away y) :
    productEquivRight x y (rightMap (R:=S) x y a)=
      algebraMap (Localization.Away y) (Iterated y x) a := by
  have h : (productEquivRight x y).toAlgHom.comp (rightMap (R:=S) x y)=
      Algebra.algHom S (Localization.Away y) (Iterated y x) := by
    apply IsLocalization.algHom_ext (Submonoid.powers y)
    ext
  exact AlgHom.congr_fun h a

theorem right_isLocalization (x y : S) :
    letI : Algebra (Localization.Away y) (Common x y) := (rightMap (R:=S) x y).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap S (Localization.Away y) x) (Common x y) := by
  letI : Algebra (Localization.Away y) (Common x y) := (rightMap (R:=S) x y).toRingHom.toAlgebra
  let e : Common x y ≃ₐ[Localization.Away y] Iterated y x :=
    { (productEquivRight x y).toRingEquiv with
      commutes' := productEquiv_rightMap x y }
  exact IsLocalization.isLocalization_of_algEquiv _ e.symm

theorem right_spec_open (x y : S) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (rightMap (R:=S) x y).toRingHom)) := by
  letI : Algebra (Localization.Away y) (Common x y) := (rightMap (R:=S) x y).toRingHom.toAlgebra
  letI := right_isLocalization x y
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (Localization.Away y) (Common x y))))
  exact IsOpenImmersion.of_isLocalization (algebraMap S (Localization.Away y) x)

theorem right_formallyEtale (x y : S) :
    letI : Algebra (Localization.Away y) (Common x y) := (rightMap (R:=S) x y).toRingHom.toAlgebra
    Algebra.FormallyEtale (Localization.Away y) (Common x y) := by
  letI : Algebra (Localization.Away y) (Common x y) := (rightMap (R:=S) x y).toRingHom.toAlgebra
  letI := right_isLocalization x y
  exact Algebra.FormallyEtale.of_isLocalization
    (Submonoid.powers (algebraMap S (Localization.Away y) x))

variable {R : Type*} [CommRing R] [Algebra R S]
theorem left_ringHom_independent_base (x y : S) :
    (leftMap (R:=R) x y).toRingHom=(leftMap (R:=S) x y).toRingHom := rfl
theorem right_ringHom_independent_base (x y : S) :
    (rightMap (R:=R) x y).toRingHom=(rightMap (R:=S) x y).toRingHom := rfl

theorem actual_left_spec_open (x y : S) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (leftMap (R:=R) x y).toRingHom)) := by
  rw [left_ringHom_independent_base]
  exact left_spec_open x y

theorem actual_right_spec_open (x y : S) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (rightMap (R:=R) x y).toRingHom)) := by
  rw [right_ringHom_independent_base]
  exact right_spec_open x y
end ProductOverlapOpen318
