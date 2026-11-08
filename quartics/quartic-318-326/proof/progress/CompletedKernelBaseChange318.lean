module
public import ZeroFiberBaseChange318
public import WeierstrassBaseChange318
public import CompletedIteratedAddition318
public section
noncomputable section
namespace CompletedKernelBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type} [CommRing R] [CommRing S] [Algebra R S]
variable (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
local notation "a" => algebraMap R S

include hD in
lemma mappedDiscriminant : IsUnit (-16*(4*(a A)^3+27*(a B)^2)) := by
  simpa only [map_neg,map_mul,map_add,map_pow,map_ofNat] using hD.map (algebraMap R S)

/-- The only remaining multiplication input is the explicit actual
tripling/coefficient square. All family and zero-section identifications
are taken from the original global coefficient construction. -/
@[expose] def data
    (hc:WeierstrassCoefficientMap318.coefficientMap (S:=S) A B ≫
        CompletedIteratedAddition318.tripling A B hD=
      CompletedIteratedAddition318.tripling (a A) (a B) (mappedDiscriminant A B hD) ≫
        WeierstrassCoefficientMap318.coefficientMap (S:=S) A B) :
    ZeroFiberBaseChange318.Data (WeierstrassGluing318.scheme A B)
      (WeierstrassGluing318.scheme (a A) (a B))
      (Spec (CommRingCat.of R)) (Spec (CommRingCat.of S)) where
  p:=WeierstrassGluing318.structureMap A B
  p':=WeierstrassGluing318.structureMap (a A) (a B)
  f:=WeierstrassCoefficientMap318.coefficientMap A B
  b:=Spec.map (CommRingCat.ofHom a)
  cartesian:=WeierstrassBaseChange318.coefficient_base_pullback A B
  t:=CompletedIteratedAddition318.tripling A B hD
  t':=CompletedIteratedAddition318.tripling (a A) (a B) (mappedDiscriminant A B hD)
  e:=WeierstrassGluing318.infinity A B
  e':=WeierstrassGluing318.infinity (a A) (a B)
  t_base:=CompletedIteratedAddition318.tripling_over_base A B hD
  t'_base:=CompletedIteratedAddition318.tripling_over_base _ _ _
  e_base:=WeierstrassGluing318.infinity_section A B
  e'_base:=WeierstrassGluing318.infinity_section (a A) (a B)
  commute:=hc
  section_map:=WeierstrassCoefficientMap318.coefficientMap_infinity A B

/-- Conditional comparison with the exact unaltered kernel objects. The
commutation input is explicit until the separate producer discharges it. -/
@[expose] def isoOfCommute
    (hc:WeierstrassCoefficientMap318.coefficientMap (S:=S) A B ≫
        CompletedIteratedAddition318.tripling A B hD=
      CompletedIteratedAddition318.tripling (a A) (a B) (mappedDiscriminant A B hD) ≫
        WeierstrassCoefficientMap318.coefficientMap (S:=S) A B) :
    pullback (CompletedIteratedAddition318.tripling (a A) (a B) (mappedDiscriminant A B hD))
        (WeierstrassGluing318.infinity (a A) (a B)) ≅
      pullback (pullback.snd (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B))
        (Spec.map (CommRingCat.ofHom a)) :=
  ZeroFiberBaseChange318.iso (data A B hD hc)
end CompletedKernelBaseChange318
