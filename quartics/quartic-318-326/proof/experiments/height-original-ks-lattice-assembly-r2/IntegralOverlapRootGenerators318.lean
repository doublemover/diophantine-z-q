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

/-- Native base-change generator equation, normalized on abstract base
rings before any concrete reciprocal scalar actions are installed. -/
lemma native_baseChange_generator {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (a : Fin 3 → R) (j : Fin 3) :
    ThreeRootOrder318.baseChange a S (1 ⊗ₜ[R] generator a j)=
      generator (fun i => algebraMap R S (a i)) j :=
  coefficientMap_generator a S j

/-- Native base change followed by the SAME radicand equality, evaluated
before concrete reciprocal tensor orders and scalar actions are installed. -/
lemma native_baseChange_parameter_generator {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (a : Fin 3 → R) (b : Fin 3 → S)
    (h : ∀ i,algebraMap R S (a i)=b i) (j : Fin 3) :
    ((ThreeRootOrder318.baseChange a S).trans
      (IntegralReciprocalRootScale318.orderParameterEquiv
        (fun i => algebraMap R S (a i)) b h))
      (1 ⊗ₜ[R] generator a j)=generator b j := by
  change IntegralReciprocalRootScale318.orderParameterEquiv _ b h
    (ThreeRootOrder318.baseChange a S (1 ⊗ₜ[R] generator a j))=generator b j
  rw [native_baseChange_generator]
  exact ThreeRootScaledGenerators318.parameter_generator _ b h j

/-- Evaluate the full root-scaled composite on abstract source carriers,
so the original nested tensor algebras need not be reconstructed by inference. -/
lemma native_overlap_generator {S A B : Type*} [CommRing S] [CommRing A]
    [CommRing B] [Algebra S A] [Algebra S B]
    (a b : Fin 3 → S) (u : Sˣ) (ha : ∀ i, IsUnit (a i))
    (h : ∀ i, b i = a i * (u:S)^2)
    (f : A ≃ₐ[S] ThreeRootOrder318.Order b)
    (g : B ≃ₐ[S] ThreeRootOrder318.Order a)
    (x : A) (y : B) (j : Fin 3)
    (hf : f x = generator b j) (hg : g y = generator a j) :
    (f.trans ((IntegralReciprocalRootScale318.orderEquiv a b u ha h).trans g.symm)) x =
      (u:S) • y :=
  overlap_value f (IntegralReciprocalRootScale318.orderEquiv a b u ha h) g
    x y (generator b j) (generator a j) (u:S) hf hg
    (ThreeRootScaledGenerators318.order_scale a b u ha h j)

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
  native_baseChange_generator (R := OpenBase R c 0) (S := CommonBase R c)
    (fun i : Fin 3 => algebraMap (Polynomial R) (OpenBase R c 0)
      (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) i)) j

#check ("FRONTIER before infinityBaseChange_generator" : String)
theorem infinityBaseChange_generator (j : Fin 3) :
    infinityBaseChange R c
      (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j)=
      generator (infinityParameter R c) j :=
  native_baseChange_parameter_generator
    (R := IntegralInfinityChart318.Base R c) (S := CommonBase R c)
    (fun i : Fin 3 => algebraMap (Polynomial R) (IntegralInfinityChart318.Base R c)
      (IntegralInfinityChart318.coefficient R c i))
    (infinityParameter R c) (infinity_parameter_map R c) j

#check ("FRONTIER before actualOverlap_generator" : String)
/-- The original finite-to-infinity overlap equivalence retains the exact
identity y_j=y0*v_j for each one of the three ratio roots. -/
theorem actualOverlap_generator (j : Fin 3) :
    actualOverlapEquiv R c (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)=
      (rootUnit R c:CommonBase R c) •
        (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j) := by
  -- Keep native intermediate orders named while applying the abstract map
  -- identity. In particular do not ask the specialized root-scale lemma to
  -- reconstruct two nested tensor algebra instances while matching the goal.
  let f := finiteBaseChange R c
  let g := infinityBaseChange R c
  let e := IntegralReciprocalRootScale318.orderEquiv
    (infinityParameter R c) (finiteParameter R c) (rootUnit R c)
    (infinityParameter_unit R c) (parameter_identity R c)
  have hf : f (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)=
      generator (finiteParameter R c) j := finiteBaseChange_generator R c j
  have hg : g (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j)=
      generator (infinityParameter R c) j := infinityBaseChange_generator R c j
  have he : e (generator (finiteParameter R c) j)=
      (rootUnit R c:CommonBase R c) • generator (infinityParameter R c) j :=
    ThreeRootScaledGenerators318.order_scale (infinityParameter R c)
      (finiteParameter R c) (rootUnit R c) (infinityParameter_unit R c)
      (parameter_identity R c) j
  -- Elaborate the abstract result WITHOUT the concrete overlap goal as
  -- its expected type. Only then rewrite the two named composite aliases.
  -- This prevents goal-driven unfolding of the nested tensor instances.
  have h := overlap_value (S := CommonBase R c) f e g
    (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)
    (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j)
    (generator (finiteParameter R c) j) (generator (infinityParameter R c) j)
    (rootUnit R c:CommonBase R c) hf hg he
  simpa only [actualOverlapEquiv, commonOrderEquiv, f, e, g] using h

#check ("FRONTIER before infinityMap_generator" : String)
/-- Restriction of every actual infinity ratio root into the original common
order is y0^-1 times its corresponding finite root. All signs and all three
factor indices are explicit. -/
theorem infinityMap_generator (j : Fin 3) :
    IntegralOverlapChartMaps318.infinityMap R c (infinityGenerator R c j)=
      (↑(rootUnit R c)⁻¹:CommonBase R c) •
        (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j) :=
  by
    change (actualOverlapEquiv R c).symm
      (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j) = _
    exact inverse_value
      (S := CommonBase R c)
      (A := CommonBase R c ⊗[OpenBase R c 0] OpenOrder R c 0)
      (B := CommonBase R c ⊗[IntegralInfinityChart318.Base R c]
        IntegralInfinityChart318.Order R c)
      (actualOverlapEquiv R c)
      (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)
      (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j)
      (rootUnit R c) (actualOverlap_generator R c j)

#check ("FRONTIER all declarations complete" : String)
end IntegralOverlapRootGenerators318
