module
public import TorusCharacterDensity318
public import OvalAddCircle318
public import NormalizedOvalIndependence318
public import ActualCyclicClosure318
public section
noncomputable section

/-! The exact normalized generators have no integer relation on the actual
oval group. The invariant-clock additive homeomorphism turns that fact into
the missing character criterion, then returns density in the original two
real embeddings and their original subspace topologies. -/
namespace ActualPairDensity318
open Set
open RealQuarticGroup318 RealQuarticAmbient318 ActualCyclicClosure318
open NormalizedOvalIndependence318 NormalizationRealEmbedding318
open OvalInvariantClock318
local instance : AddCommGroup (Oval 1) := group 1 (by norm_num)
local instance ovalGroup (e : Fin 2) : AddCommGroup (Oval (d e)) :=
  group _ (lt_trans zero_lt_one (d_gt_one e))
set_option maxHeartbeats 2000000

@[expose] def unitToOval : UnitAddCircle ≃+ Oval 1 :=
  (AddCircle.equivAddCircle 1 period one_ne_zero period_pos.ne').trans OvalAddCircle318.circleAddEquiv

@[expose] def unitToOvalHomeomorph : UnitAddCircle ≃ₜ Oval 1 :=
  (AddCircle.homeomorphAddCircle 1 period one_ne_zero period_pos.ne').trans
    OvalAddCircle318.circleHomeomorph

@[expose] def root (e : Fin 2) : ℝ := if e=0 then alpha else beta

lemma root_pos (e : Fin 2) : 0<root e := by
  fin_cases e <;> simp [root,alpha_pos,beta_pos]

lemma root_pow (e : Fin 2) : (root e)^4=d e := by
  fin_cases e
  · simpa [root,d,embedding] using positive_coefficient.symm
  · simpa [root,d,embedding] using negative_coefficient.symm

@[expose] def normalization (e : Fin 2) : Oval (d e) ≃+ Oval 1 :=
  RealOvalNormalization318.ovalAddEquiv _ (lt_trans zero_lt_one (d_gt_one e))
    (root e) (root_pos e) (root_pow e)

@[expose] def normalizationHomeomorph (e : Fin 2) : Oval (d e) ≃ₜ Oval 1 :=
  RealOvalNormalization318.ovalHomeomorph _ (root e) (root_pos e) (root_pow e)

@[expose] def coordinateEquiv (e : Fin 2) : Oval (d e) ≃+ UnitAddCircle :=
  (normalization e).trans unitToOval.symm

@[expose] def pairEquiv : Pair ≃+ UnitAddTorus (Fin 2) where
  toFun p e := coordinateEquiv e (p e)
  invFun p e := (coordinateEquiv e).symm (p e)
  left_inv p := by funext e; exact (coordinateEquiv e).symm_apply_apply _
  right_inv p := by funext e; exact (coordinateEquiv e).apply_symm_apply _
  map_add' p q := by funext e; exact map_add (coordinateEquiv e) _ _

@[expose] def pairHomeomorph : Pair ≃ₜ UnitAddTorus (Fin 2) :=
  { pairEquiv.toEquiv with
    continuous_toFun := continuous_pi fun e =>
      unitToOvalHomeomorph.symm.continuous.comp
        ((normalizationHomeomorph e).continuous.comp (continuous_apply e))
    continuous_invFun := continuous_pi fun e =>
      (normalizationHomeomorph e).symm.continuous.comp
        (unitToOvalHomeomorph.continuous.comp (continuous_apply e)) }

lemma first_generator : unitToOval ((pairEquiv generator) 0)=firstOvalGenerator := by
  change unitToOval (unitToOval.symm (normalization 0 (generator 0)))=firstOvalGenerator
  rw [unitToOval.apply_symm_apply]
  apply Subtype.ext
  simp [normalization,RealOvalNormalization318.ovalAddEquiv,RealOvalNormalization318.ovalEquiv,
    RealOvalNormalization318.forward,root,generator,pairOrbit,embedding,d,
    firstOvalGenerator,positiveEquiv]

lemma second_generator : unitToOval ((pairEquiv generator) 1)=secondOvalGenerator := by
  change unitToOval (unitToOval.symm (normalization 1 (generator 1)))=secondOvalGenerator
  rw [unitToOval.apply_symm_apply]
  apply Subtype.ext
  simp [normalization,RealOvalNormalization318.ovalAddEquiv,RealOvalNormalization318.ovalEquiv,
    RealOvalNormalization318.forward,root,generator,pairOrbit,embedding,d,
    secondOvalGenerator,negativeEquiv]

/-- The no-character-relation hypothesis is produced from the exact original
arithmetic generators, not supplied by the caller. -/
theorem no_character_relation (n : Fin 2 → ℤ) (hn : n≠0) :
    UnitAddTorus.mFourier n (pairEquiv generator)≠1 := by
  intro he
  have hc : (AddCircle.toCircle
      (n 0 • (pairEquiv generator) 0+n 1 • (pairEquiv generator) 1) : ℂ)=1 := by
    simpa only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,
      fourier_apply,AddCircle.toCircle_add,Circle.coe_mul] using he
  have hs : n 0 • (pairEquiv generator) 0+n 1 • (pairEquiv generator) 1=0 := by
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa using hc
  have ho := congrArg unitToOval hs
  simp only [map_add,map_zsmul,map_zero,first_generator,second_generator] at ho
  obtain ⟨h0,h1⟩ := oval_integer_relation (n 0) (n 1) ho
  apply hn
  funext e
  fin_cases e <;> assumption

/-- Full density in the literal pair of real quartic ovals. This theorem
closes the real-input premise of DenseOrbitCRTPrefix318. -/
theorem pairOrbit_dense : DenseRange pairOrbit := by
  have hd : DenseRange (fun k : ℤ => k • pairEquiv generator) :=
    TorusCharacterDensity318.denseRange_zsmul _ no_character_relation
  have ht := pairHomeomorph.symm.surjective.denseRange.comp hd
    pairHomeomorph.symm.continuous
  have he : (fun k : ℤ => pairHomeomorph.symm (k • pairEquiv generator))=pairOrbit := by
    funext k
    change pairEquiv.symm (k • pairEquiv generator)=pairOrbit k
    rw [map_zsmul,pairEquiv.symm_apply_apply,pairOrbit_zsmul]
  rwa [he] at ht

end ActualPairDensity318
