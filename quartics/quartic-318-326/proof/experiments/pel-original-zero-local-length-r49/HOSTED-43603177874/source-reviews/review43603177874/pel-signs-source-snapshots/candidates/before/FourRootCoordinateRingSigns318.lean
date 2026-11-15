module
public import FourRootInfinityCoordinateRing318
public import FourRootNormalizedSignAction318
public section
noncomputable section
namespace FourRootCoordinateRingSigns318
open FourBinaryCharacters318
variable (b:Fin 4→ℂ) (g:FourBinaryCharacters318.Group)

lemma scalar_square (S:Type*) [CommRing S] [Algebra ℂ S] (i:Fin 4):
    (algebraMap ℂ S (coordinate (F:=ℂ) i g))^2=1:=by
  rw [←map_pow,coordinate_square,map_one]
lemma double_scalar_square (S:Type*) [CommRing S] [Algebra ℂ S] (i:Fin 4):
    (algebraMap ℂ S (coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g))^2=1:=by
  rw [←map_pow,mul_pow,coordinate_square,coordinate_square,one_mul,map_one]

/-- Genuine algebra endomorphism of the exact finite coordinate ring,
not an action transported from a complex point bijection. -/
@[expose] def finiteEnd : FourRootAffineCoordinateRing318.Ring b→ₐ[ℂ]FourRootAffineCoordinateRing318.Ring b:=
  FourRootAffineCoordinateRing318.lift b (FourRootAffineCoordinateRing318.coordinate b none)
    (fun i=>algebraMap ℂ _ (coordinate (F:=ℂ) i g)*FourRootAffineCoordinateRing318.coordinate b (some i)) (by
      intro i
      rw [mul_pow,scalar_square,one_mul]
      exact FourRootAffineCoordinateRing318.relation b i)
lemma finite_base:finiteEnd b g (FourRootAffineCoordinateRing318.coordinate b none)=
    FourRootAffineCoordinateRing318.coordinate b none:=FourRootAffineCoordinateRing318.lift_coordinate _ _ _ _ _
lemma finite_root (i:Fin 4):finiteEnd b g (FourRootAffineCoordinateRing318.coordinate b (some i))=
    algebraMap ℂ _ (coordinate (F:=ℂ) i g)*FourRootAffineCoordinateRing318.coordinate b (some i):=
  FourRootAffineCoordinateRing318.lift_coordinate _ _ _ _ _
lemma finite_involutive : Function.Involutive (finiteEnd b g) := by
  have he:(finiteEnd b g).comp (finiteEnd b g)=AlgHom.id ℂ (FourRootAffineCoordinateRing318.Ring b):=by
    apply FourRootAffineCoordinateRing318.hom_ext
    intro k
    cases k with
    | none=>simp only [AlgHom.comp_apply,finite_base,AlgHom.id_apply]
    | some i=>
      simp only [AlgHom.comp_apply,finite_root,map_mul,AlgHom.commutes,AlgHom.id_apply]
      rw [←mul_assoc,←pow_two,scalar_square,one_mul]
  intro x
  exact AlgHom.congr_fun he x
@[expose] def finiteEquiv : FourRootAffineCoordinateRing318.Ring b≃ₐ[ℂ]FourRootAffineCoordinateRing318.Ring b where
  toFun:=finiteEnd b g
  invFun:=finiteEnd b g
  left_inv:=finite_involutive b g
  right_inv:=finite_involutive b g
  map_mul':=(finiteEnd b g).map_mul
  map_add':=(finiteEnd b g).map_add
  commutes':=(finiteEnd b g).commutes

/-- The infinity algebra action keeps the normalization s0=1 and uses
u↦epsilon0*u, s_i↦epsilon_i*epsilon0*s_i. -/
@[expose] def infinityEnd : FourRootInfinityCoordinateRing318.Ring b→ₐ[ℂ]FourRootInfinityCoordinateRing318.Ring b:=
  FourRootInfinityCoordinateRing318.lift b
    (algebraMap ℂ _ (coordinate (F:=ℂ) 0 g)*FourRootInfinityCoordinateRing318.coordinate b none)
    (fun i=>algebraMap ℂ _ (coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g)*
      FourRootInfinityCoordinateRing318.coordinate b (some i)) (by
      rw [←pow_two,coordinate_square,map_one,one_mul,FourRootInfinityCoordinateRing318.zero_relation]) (by
      intro i
      rw [mul_pow,double_scalar_square,one_mul,mul_pow,scalar_square,one_mul]
      exact FourRootInfinityCoordinateRing318.relation b i)
lemma infinity_parameter:infinityEnd b g (FourRootInfinityCoordinateRing318.coordinate b none)=
    algebraMap ℂ _ (coordinate (F:=ℂ) 0 g)*FourRootInfinityCoordinateRing318.coordinate b none:=
  FourRootInfinityCoordinateRing318.lift_coordinate _ _ _ _ _ _
lemma infinity_ratio (i:Fin 4):infinityEnd b g (FourRootInfinityCoordinateRing318.coordinate b (some i))=
    algebraMap ℂ _ (coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g)*
      FourRootInfinityCoordinateRing318.coordinate b (some i):=
  FourRootInfinityCoordinateRing318.lift_coordinate _ _ _ _ _ _
lemma infinity_involutive : Function.Involutive (infinityEnd b g) := by
  have he:(infinityEnd b g).comp (infinityEnd b g)=AlgHom.id ℂ (FourRootInfinityCoordinateRing318.Ring b):=by
    apply FourRootInfinityCoordinateRing318.hom_ext
    intro k
    cases k with
    | none=>
      simp only [AlgHom.comp_apply,infinity_parameter,map_mul,AlgHom.commutes,AlgHom.id_apply]
      rw [←mul_assoc,←pow_two,scalar_square,one_mul]
    | some i=>
      simp only [AlgHom.comp_apply,infinity_ratio,map_mul,AlgHom.commutes,AlgHom.id_apply]
      rw [←mul_assoc,←pow_two,double_scalar_square,one_mul]
  intro x
  exact AlgHom.congr_fun he x
@[expose] def infinityEquiv : FourRootInfinityCoordinateRing318.Ring b≃ₐ[ℂ]FourRootInfinityCoordinateRing318.Ring b where
  toFun:=infinityEnd b g
  invFun:=infinityEnd b g
  left_inv:=infinity_involutive b g
  right_inv:=infinity_involutive b g
  map_mul':=(infinityEnd b g).map_mul
  map_add':=(infinityEnd b g).map_add
  commutes':=(infinityEnd b g).commutes

/-- Evaluation intertwines the actual algebra action and exact signed
finite point map. This is equality on every complex-valued algebra point. -/
lemma finite_point (f:FourRootAffineCoordinateRing318.Ring b→ₐ[ℂ]ℂ):
    FourRootAffineCoordinateRing318.point b (f.comp (finiteEnd b g))=
      FourRootNormalizedSignAction318.finite b g (FourRootAffineCoordinateRing318.point b f) := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg f (finite_base b g)
  · funext i
    change f (finiteEnd b g (FourRootAffineCoordinateRing318.coordinate b (some i)))=_
    rw [finite_root,map_mul,AlgHom.commutes,Algebra.algebraMap_self_apply]
    rfl
lemma infinity_point (f:FourRootInfinityCoordinateRing318.Ring b→ₐ[ℂ]ℂ):
    FourRootInfinityCoordinateRing318.point b (f.comp (infinityEnd b g))=
      FourRootNormalizedSignAction318.infinity b g (FourRootInfinityCoordinateRing318.point b f) := by
  apply Subtype.ext
  apply Prod.ext
  · change f (infinityEnd b g (FourRootInfinityCoordinateRing318.coordinate b none))=_
    rw [infinity_parameter,map_mul,AlgHom.commutes,Algebra.algebraMap_self_apply]
    rfl
  · funext i
    change f (infinityEnd b g (FourRootInfinityCoordinateRing318.coordinate b (some i)))=_
    rw [infinity_ratio,map_mul,AlgHom.commutes,Algebra.algebraMap_self_apply]
    rfl
end FourRootCoordinateRingSigns318
