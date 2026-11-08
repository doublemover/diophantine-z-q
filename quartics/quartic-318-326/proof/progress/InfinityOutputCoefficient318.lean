module
public import FinitePairCoefficient318
public section
noncomputable section
namespace InfinityOutputCoefficient318
open FinitePairCoefficient318 InfinityAdditionAlgebra318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S
@[expose] def map (A B:R) (t:Bool) : OutputRing A B t →ₐ[R] OutputRing (a A) (a B) t := by
  cases t
  · exact localMap (S:=S) A B 2
  · exact localMap (S:=S) A B 3
@[simp] theorem map_base (A B:R) (t:Bool) (x:PairRing A B) :
    map (S:=S) A B t (pairMap A B t x)=pairMap (a A) (a B) t (pair (S:=S) A B x) := by
  cases t <;> exact localMap_base A B _ x

lemma inverse_map {U V:Type*} [CommRing U] [CommRing V] (f:U →+* V) (u:Uˣ) (v:Vˣ)
    (h:f (u:U)=(v:V)) : f (↑u⁻¹:U)=(↑v⁻¹:V) := by
  have he:Units.map f.toMonoidHom u=v:=Units.ext h
  exact congrArg (fun w:Vˣ=>(↑w⁻¹:V)) he
lemma map_inverse (A B:R) (t:Bool) :
    map (S:=S) A B t (↑(numeratorYUnit A B t)⁻¹)=↑(numeratorYUnit (a A) (a B) t)⁻¹ := by
  apply inverse_map (map (S:=S) A B t).toRingHom
  change map (S:=S) A B t ((numeratorY_unit A B t).unit:OutputRing A B t)=_
  rw [IsUnit.unit_spec,show (numeratorYUnit (a A) (a B) t:OutputRing (a A) (a B) t)=pairMap (a A) (a B) t (numeratorY (a A) (a B) t) from IsUnit.unit_spec _]
  rw [map_base,pair_numeratorY]
@[simp] lemma map_outX (A B:R) (t:Bool) : map (S:=S) A B t (outX A B t)=outX (a A) (a B) t := by
  simp only [outX,map_mul,map_base,pair_numeratorX,pair_denominator,map_inverse]
@[simp] lemma map_outZ (A B:R) (t:Bool) : map (S:=S) A B t (outZ A B t)=outZ (a A) (a B) t := by
  simp only [outZ,map_mul,map_pow,map_base,pair_denominator,map_inverse]
theorem output (A B:R) (t:Bool) : (map (S:=S) A B t).comp (outputMap A B t)=
    ((outputMap (a A) (a B) t).restrictScalars R).comp (InfinityBaseChange318.coefficientMap (S:=S) A B) := by
  apply InfinityChart318.hom_ext
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,outputMap_x,InfinityBaseChange318.coefficientMap_x,map_outX]
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,outputMap_z,InfinityBaseChange318.coefficientMap_z,map_outZ]
end InfinityOutputCoefficient318
