module
public import FourRootCoordinateOverlap318
public import FourRootCoordinateRingSigns318
public section
noncomputable section
namespace FourRootLocalizedSignAction318
open FourRootCoordinateOverlap318 FourRootCoordinateRingSigns318
variable (b:Fin 4→ℂ) (g:FourBinaryCharacters318.Group)
@[expose] def epsilon (i:Fin 4):InfinityOverlap b:=
  algebraMap ℂ _ (FourBinaryCharacters318.coordinate (F:=ℂ) i g)
lemma epsilon_square (i:Fin 4):epsilon b g i^2=1:=by
  rw [epsilon,←map_pow,FourBinaryCharacters318.coordinate_square,map_one]
@[expose] def localizedBase:Infinity b→ₐ[ℂ]InfinityOverlap b:=
  (IsScalarTower.toAlgHom ℂ (Infinity b) (InfinityOverlap b)).comp (infinityEnd b g)
lemma localizedBase_u:localizedBase b g (FourRootInfinityCoordinateRing318.coordinate b none)=
    epsilon b g 0*u b:=by
  simp [localizedBase,infinity_parameter,epsilon,u,←IsScalarTower.algebraMap_apply]
lemma localizedBase_s (i:Fin 4):localizedBase b g (FourRootInfinityCoordinateRing318.coordinate b (some i))=
    epsilon b g i*epsilon b g 0*s b i:=by
  simp [localizedBase,infinity_ratio,epsilon,s,←IsScalarTower.algebraMap_apply,map_mul,mul_assoc]

/-- Actual endomorphism of the common principal localization. Its
existence uses the genuine unit u, with the original sign scalar. -/
@[expose] def overlapEnd:InfinityOverlap b→ₐ[ℂ]InfinityOverlap b:=
  IsLocalization.Away.liftAlgHom (f:=localizedBase b g)
    (FourRootInfinityCoordinateRing318.coordinate b none) (by
      rw [localizedBase_u]
      apply IsUnit.of_mul_eq_one_right (epsilon b g 0*ui b)
      calc
        (epsilon b g 0*ui b)*(epsilon b g 0*u b)=
          epsilon b g 0^2*(u b*ui b):=by ring
        _=1:=by rw [epsilon_square,u_ui,one_mul])
@[simp] lemma overlap_map (a:Infinity b):
    overlapEnd b g (algebraMap (Infinity b) (InfinityOverlap b) a)=localizedBase b g a:=by
  simp [overlapEnd,IsLocalization.Away.liftAlgHom_apply]
@[simp] lemma overlap_u:overlapEnd b g (u b)=epsilon b g 0*u b:=by
  exact (overlap_map b g _).trans (localizedBase_u b g)
@[simp] lemma overlap_s (i:Fin 4):overlapEnd b g (s b i)=epsilon b g i*epsilon b g 0*s b i:=by
  exact (overlap_map b g _).trans (localizedBase_s b g i)
lemma overlap_ui:overlapEnd b g (ui b)=epsilon b g 0*ui b:=by
  have he:=congrArg (overlapEnd b g) (u_ui b)
  simp only [map_mul,map_one,overlap_u] at he
  have hc:(epsilon b g 0*ui b)*(epsilon b g 0*u b)=1:=by
    calc
      _=epsilon b g 0^2*(u b*ui b):=by ring
      _=1:=by rw [epsilon_square,u_ui,one_mul]
  calc
    _=((epsilon b g 0*ui b)*(epsilon b g 0*u b))*overlapEnd b g (ui b):=by rw [hc,one_mul]
    _=(epsilon b g 0*ui b)*((epsilon b g 0*u b)*overlapEnd b g (ui b)):=by ring
    _=epsilon b g 0*ui b:=by rw [he,mul_one]

/-- Exact covariance of the finite-to-infinity algebra map on ALL
original quotient generators, not only after evaluating complex points. -/
lemma finite_square:(overlapEnd b g).comp (toInfinityBase b)=
    (toInfinityBase b).comp (finiteEnd b g):=by
  apply FourRootAffineCoordinateRing318.hom_ext
  intro k
  cases k with
  | none=>
    simp only [AlgHom.comp_apply,toInfinityBase_t,finite_base,map_add,map_pow,
      AlgHom.commutes,overlap_ui,mul_pow,epsilon_square,one_mul]
  | some i=>
    simp only [AlgHom.comp_apply,toInfinityBase_z,finite_root,map_mul,AlgHom.commutes,
      overlap_s,overlap_ui]
    change (epsilon b g i*epsilon b g 0*s b i)*(epsilon b g 0*ui b)=
      epsilon b g i*(s b i*ui b)
    calc
      _=epsilon b g i*(s b i*ui b)*epsilon b g 0^2:=by ring
      _=epsilon b g i*(s b i*ui b):=by rw [epsilon_square,mul_one]
lemma infinity_square:(overlapEnd b g).comp
    (IsScalarTower.toAlgHom ℂ (Infinity b) (InfinityOverlap b))=
    (IsScalarTower.toAlgHom ℂ (Infinity b) (InfinityOverlap b)).comp (infinityEnd b g):=by
  ext a
  exact overlap_map b g a
end FourRootLocalizedSignAction318
