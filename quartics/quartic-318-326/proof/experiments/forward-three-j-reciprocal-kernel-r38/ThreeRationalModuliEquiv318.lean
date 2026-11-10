module
public import ThreeRationalModuliInverse318
public section
noncomputable section
namespace ThreeRationalModuliEquiv318
open ThreeJArithmeticAlgebraMap318 ThreeRationalModuliInverse318
open scoped TensorProduct
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original j and torsion-x generators separate maps into any
commutative ring. The statement does not require a field or reduced target. -/
lemma fixed_hom_ext {R : Type*} [CommRing R] (f g : Fixed →+* R)
    (hj : f (algebraMap (OpenJModel318.Base 3) Fixed (OpenJModel318.jCoord 3))=
      g (algebraMap (OpenJModel318.Base 3) Fixed (OpenJModel318.jCoord 3)))
    (hx : f (ModularArithmeticCoordinates318.xGenerator 3)=
      g (ModularArithmeticCoordinates318.xGenerator 3)) : f=g := by
  have hb : f.comp (algebraMap (OpenJModel318.Base 3) Fixed)=
      g.comp (algebraMap (OpenJModel318.Base 3) Fixed) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator 3))
    apply Polynomial.ringHom_ext
    · intro n
      simp
    · exact hj
  have he : f.comp fixedEquiv.toRingEquiv.toRingHom=
      g.comp fixedEquiv.toRingEquiv.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · rw [←AdjoinRoot.algebraMap_eq]
      apply RingHom.ext
      intro r
      change f (fixedEquiv (algebraMap (OpenJModel318.Base 3) XRing r))=
        g (fixedEquiv (algebraMap (OpenJModel318.Base 3) XRing r))
      rw [AlgEquiv.commutes]
      exact RingHom.congr_fun hb r
    · exact hx
  apply RingHom.ext
  intro r
  obtain ⟨a,rfl⟩ := fixedEquiv.surjective r
  exact RingHom.congr_fun he a

lemma backward_fixed : backward.toRingHom.comp fixedMap=
    ThreeRationalFixed318.includeFixed.toRingHom := by
  refine fixed_hom_ext (R := ThreeRationalFixed318.Ring)
    (backward.toRingHom.comp fixedMap) ThreeRationalFixed318.includeFixed.toRingHom ?_ ?_
  · change backward (fixedMap _)=_
    rw [fixedMap_j,backward_j]
    rfl
  · change backward (fixedMap _)=_
    rw [fixedMap_x,backward_x]
    rfl

lemma forward_backward : forward.comp backward=AlgHom.id ℚ ThreeJModuliOpen318.Ring := by
  apply IsLocalization.algHom_ext (Submonoid.powers ThreeJModuliOpen318.deleted)
  apply IsLocalization.algHom_ext (Submonoid.powers (Polynomial.X:Polynomial ℚ))
  apply Polynomial.algHom_ext
  change forward (backward ThreeJModuliOpen318.t)=ThreeJModuliOpen318.t
  rw [backward_t,forward_parameter]

lemma backward_forward : backward.comp forward=AlgHom.id ℚ ThreeRationalFixed318.Ring := by
  apply AlgHom.ext
  intro t
  change backward (forward t)=t
  induction t using TensorProduct.inductionOn with
  | tmul q a =>
    have he : q ⊗ₜ[ℤ] a = q • ThreeRationalFixed318.includeFixed a := by
      change q ⊗ₜ[ℤ] a = q • ((1 : ℚ) ⊗ₜ[ℤ] a)
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    have hf : forward (q • ThreeRationalFixed318.includeFixed a)=
        q • forward (ThreeRationalFixed318.includeFixed a) :=
      forward.toLinearMap.map_smul q (ThreeRationalFixed318.includeFixed a)
    have hb : backward (q • forward (ThreeRationalFixed318.includeFixed a))=
        q • backward (forward (ThreeRationalFixed318.includeFixed a)) :=
      backward.toLinearMap.map_smul q (forward (ThreeRationalFixed318.includeFixed a))
    rw [he,hf,hb,forward_fixed]
    exact congrArg (fun z : ThreeRationalFixed318.Ring => q • z)
      (RingHom.congr_fun backward_fixed a)
  | add x y hx hy =>
    rw [map_add,map_add,hx,hy]

/-- Actual Q-algebra isomorphism between the rational base change of the
original diamond-fixed algebra and the original rational parameter open.
Both inverse maps are constructed by universal properties and proved inverse
inside the rings; complex-point bijectivity plays no role in this proof. -/
@[expose] def equivalence : ThreeRationalFixed318.Ring ≃ₐ[ℚ] ThreeJModuliOpen318.Ring :=
  AlgEquiv.ofAlgHom forward backward forward_backward backward_forward
lemma equivalence_fixed (a : Fixed) :
    equivalence (ThreeRationalFixed318.includeFixed a)=fixedMap a := forward_fixed a
lemma equivalence_j : equivalence ThreeRationalFixed318.j=ThreeJModuliOpen318.j := forward_j
lemma equivalence_x : equivalence ThreeRationalFixed318.x=ThreeJModuliOpen318.x := forward_x
lemma inverse_parameter : equivalence.symm ThreeJModuliOpen318.t=ThreeRationalFixed318.parameter :=
  backward_t

end ThreeRationalModuliEquiv318
