module
public import ThreeRootScaledGenerators318
public section
noncomputable section
namespace IntegralOverlapRootGenerators318
open IntegralSourceBranches318 IntegralInfinityCommonBase318 IntegralInfinityCommonOrder318
open IntegralInfinityOverlapRealization318 IntegralOverlapChartMaps318 ThreeRootCoordinates318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section Abstract
variable {S A B C D : Type*} [CommRing S] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra S A] [Algebra S B]
    [Algebra S C] [Algebra S D]

#check ("FRONTIER before trans_value" : String)
/-- Reduce a composite equivalence before installing the concrete tensor orders. -/
private lemma trans_value (f : A ≃ₐ[S] B) (g : B ≃ₐ[S] C)
    (a : A) (b : B) (c : C) (hf : f a=b) (hg : g b=c) :
    (f.trans g) a=c := by
  change g (f a)=c
  rw [hf]
  exact hg

#check ("FRONTIER before overlap_value" : String)
/-- The same finite-to-infinity composite, evaluated on abstract carriers. -/
private lemma overlap_value (f : A ≃ₐ[S] C) (h : C ≃ₐ[S] D)
    (g : B ≃ₐ[S] D) (a : A) (b : B) (a' : C) (b' : D) (r : S)
    (hf : f a=a') (hg : g b=b') (hh : h a'=r • b') :
    (f.trans (h.trans g.symm)) a=r • b := by
  apply g.injective
  change g (g.symm (h (f a)))=g (r • b)
  rw [AlgEquiv.apply_symm_apply,hf,hh,map_smul,hg]

#check ("FRONTIER before inverse_value" : String)
/-- Invert the same unit-scaled root equation on abstract carriers. -/
private lemma inverse_value (e : A ≃ₐ[S] B) (a : A) (b : B) (u : Sˣ)
    (h : e a=(u:S) • b) : e.symm b=(↑u⁻¹:S) • a := by
  apply e.injective
  rw [AlgEquiv.apply_symm_apply,map_smul,h,smul_smul,Units.inv_mul,one_smul]
end Abstract

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
#check ("FRONTIER before infinityAlgebra" : String)
local instance infinityAlgebra :
    Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra

#check ("FRONTIER before finiteGenerator" : String)
@[expose] def finiteGenerator (j : Fin 3) : OpenOrder R c 0 :=
  generator (R := OpenBase R c 0) (fun i => algebraMap (Polynomial R) (OpenBase R c 0)
    (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) i)) j
#check ("FRONTIER before infinityGenerator" : String)
@[expose] def infinityGenerator (j : Fin 3) : IntegralInfinityChart318.Order R c :=
  generator (R := IntegralInfinityChart318.Base R c)
    (fun i => algebraMap (Polynomial R) (IntegralInfinityChart318.Base R c)
    (IntegralInfinityChart318.coefficient R c i)) j

#check ("FRONTIER before finiteBaseChange_generator" : String)
theorem finiteBaseChange_generator (j : Fin 3) :
    finiteBaseChange R c (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)=
      generator (finiteParameter R c) j :=
  coefficientMap_generator _ (CommonBase R c) j

#check ("FRONTIER before infinityBaseChange_generator" : String)
theorem infinityBaseChange_generator (j : Fin 3) :
    infinityBaseChange R c
      (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j)=
      generator (infinityParameter R c) j :=
  trans_value (ThreeRootOrder318.baseChange _ (CommonBase R c))
    (IntegralReciprocalRootScale318.orderParameterEquiv _ _ (infinity_parameter_map R c))
    _ _ _ (coefficientMap_generator _ (CommonBase R c) j)
    (ThreeRootScaledGenerators318.parameter_generator _ _ (infinity_parameter_map R c) j)

#check ("FRONTIER before actualOverlap_generator" : String)
/-- The original finite-to-infinity overlap equivalence retains the exact
identity y_j=y0*v_j for each one of the three ratio roots. -/
theorem actualOverlap_generator (j : Fin 3) :
    actualOverlapEquiv R c (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)=
      (rootUnit R c:CommonBase R c) •
        (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j) :=
  overlap_value (finiteBaseChange R c)
    (IntegralReciprocalRootScale318.orderEquiv _ _ (rootUnit R c)
      (infinityParameter_unit R c) (parameter_identity R c))
    (infinityBaseChange R c) _ _ _ _ (rootUnit R c : CommonBase R c)
    (finiteBaseChange_generator R c j) (infinityBaseChange_generator R c j)
    (ThreeRootScaledGenerators318.order_scale _ _ (rootUnit R c)
      (infinityParameter_unit R c) (parameter_identity R c) j)

#check ("FRONTIER before infinityMap_generator" : String)
/-- Restriction of every actual infinity ratio root into the original common
order is y0^-1 times its corresponding finite root. All signs and all three
factor indices are explicit. -/
theorem infinityMap_generator (j : Fin 3) :
    IntegralOverlapChartMaps318.infinityMap R c (infinityGenerator R c j)=
      (↑(rootUnit R c)⁻¹:CommonBase R c) •
        (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j) :=
  inverse_value (actualOverlapEquiv R c) _ _ (rootUnit R c)
    (actualOverlap_generator R c j)

#check ("FRONTIER all declarations complete" : String)
end IntegralOverlapRootGenerators318
