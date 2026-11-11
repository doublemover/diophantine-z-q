module
public import FramedLineMorphismCoefficient318
public import LineSheafInverse318
public section
noncomputable section
namespace FramedLineMorphismContraction318
open AlgebraicGeometry CategoryTheory Opposite ModuleLocalGluing318
universe u
variable {X:Scheme.{u}} {ι:Type u} (M N:X.Modules) (U:ι→X.Opens)
  (e:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
  (f:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅N.restrict (U i).ι)
  (d:M⟶N)
@[expose] def object:X.Modules:=
  IntrinsicTensorSheaf318.tensor (LineSheafInverse318.object N U f) M
@[expose] def frames(i:ι):SheafOfModules.unit (U i).toScheme.ringCatSheaf≅
    (object M N U f).restrict (U i).ι:=
  TensorLineCocycle318.frames (LineSheafInverse318.object N U f) M U
    (LineSheafInverse318.frame N U f) e i
abbrev coordinate(i:ι)(V:X.Opens)(h:V≤U i):=
  (OpenLineFrameCoordinates318.frame (object M N U f) (U i) (frames M N U e f i) V h).symm
@[expose] def localMap(i:ι)(V:X.Opens)(h:V≤U i):
    Γ(object M N U f,V)→ₗ[Γ(X,V)]Γ(X,V) where
  toFun s:=coordinate M N U e f i V h s*FramedLineMorphismCoefficient318.coefficient M N U e f d i V h
  map_add' s t:=by rw [map_add,add_mul]
  map_smul' a s:=by rw [map_smul,smul_eq_mul,smul_eq_mul,mul_assoc]
lemma natural(i:ι)(V W:X.Opens)(hV:V≤U i)(hW:W≤V)(s:Γ(object M N U f,V)):
    X.presheaf.map (homOfLE hW).op (localMap M N U e f d i V hV s)=
      localMap M N U e f d i W (hW.trans hV) (res (object M N U f) hW s):=by
  change X.presheaf.map _ (_*_)=_ * _
  rw [map_mul,OpenLineFrameCoordinates318.inverse_natural,
    FramedLineMorphismCoefficient318.natural]
lemma cocycle:
    LineFrameCocycle318.cocycle (object M N U f) U (frames M N U e f)=
      UnitCocycleProduct318.product
        (UnitCocycleInverse318.inverse (LineFrameCocycle318.cocycle N U f))
        (LineFrameCocycle318.cocycle M U e):=by
  rw [frames,object,TensorLineCocycle318.cocycle_eq,
    LineSheafInverse318.original_inverse_transitions]
/-- The actual arrow coefficients and the inverse-target/source tensor
coordinates transform oppositely on full overlaps, so contraction glues
without choosing a rational trivialization or ignoring any zero. -/
lemma compatible(i j:ι)(V:X.Opens)(hi:V≤U i)(hj:V≤U j)(s:Γ(object M N U f,V)):
    localMap M N U e f d i V hi s=localMap M N U e f d j V hj s:=by
  let r:=X.presheaf.map (homOfLE (le_inf hi hj)).op
  let a:=(LineFrameCocycle318.cocycle M U e).transition i j
  let b:=(LineFrameCocycle318.cocycle N U f).transition i j
  let ci:=FramedLineMorphismCoefficient318.coefficient M N U e f d i V hi
  let cj:=FramedLineMorphismCoefficient318.coefficient M N U e f d j V hj
  let kj:=coordinate M N U e f j V hj s
  have hc:ci*r a.val=r b.val*cj:=FramedLineMorphismCoefficient318.transition M N U e f d i j V hi hj
  have hk:=FramedLineMorphismCoefficient318.coordinate_transition U (frames M N U e f) i j V hi hj s
  rw [cocycle] at hk
  simp only [UnitCocycleProduct318.product,UnitCocycleInverse318.inverse,
    Units.val_mul,map_mul] at hk
  have hb:r (b⁻¹).val*r b.val=1:=by rw [←map_mul,Units.inv_mul,map_one]
  change coordinate M N U e f i V hi s*ci=kj*cj
  rw [hk]
  change (r (b⁻¹).val*r a.val*kj)*ci=kj*cj
  calc
    _=r (b⁻¹).val*kj*(ci*r a.val):=by ring
    _=r (b⁻¹).val*kj*(r b.val*cj):=by rw [hc]
    _=(r (b⁻¹).val*r b.val)*(kj*cj):=by ring
    _=kj*cj:=by rw [hb,one_mul]
@[expose] def data:LocalData (object M N U f) (SheafOfModules.unit X.ringCatSheaf) U where
  map:=localMap M N U e f d
  natural:=natural M N U e f d
  compatible:=compatible M N U e f d
variable (hc:(⊤:X.Opens)≤⨆i,U i)
/-- Genuine global O-linear contraction N^{-1} tensor M -> O_X,
constructed from the SAME original line-to-line morphism d:M->N. -/
@[expose] def hom:object M N U f⟶SheafOfModules.unit X.ringCatSheaf:=
  ModuleLocalGluing318.hom (data M N U e f d) hc
lemma hom_on_subopen(i:ι)(V:X.Opens)(h:V≤U i)(s:Γ(object M N U f,V)):
    (hom M N U e f d hc).app V s=localMap M N U e f d i V h s:=by
  have ht:=ModuleLocalGluing318.value_subopen (data M N U e f d) hc V V le_rfl i h s
  simpa only [res_self] using ht
lemma range_on_subopen(i:ι)(V:X.Opens)(h:V≤U i):
    LinearMap.range ((hom M N U e f d hc).val.app (op V)).hom=
      Ideal.span {FramedLineMorphismCoefficient318.coefficient M N U e f d i V h}:=by
  ext a
  constructor
  · rintro ⟨s,rfl⟩
    rw [hom_on_subopen M N U e f d hc i V h]
    exact Ideal.mem_span_singleton'.mpr ⟨coordinate M N U e f i V h s,rfl⟩
  · intro ha
    obtain ⟨c,hc⟩:=Ideal.mem_span_singleton'.mp ha
    refine ⟨(coordinate M N U e f i V h).symm c,?_⟩
    rw [hom_on_subopen]
    change coordinate M N U e f i V h ((coordinate M N U e f i V h).symm c)*_=a
    rw [LinearEquiv.apply_symm_apply]
    exact hc
lemma injective_on_subopen(i:ι)(V:X.Opens)(h:V≤U i)
    (hr:∀a:Γ(X,V),a*FramedLineMorphismCoefficient318.coefficient M N U e f d i V h=0→a=0):
    Function.Injective ((hom M N U e f d hc).app V):=by
  intro s t hst
  apply (coordinate M N U e f i V h).injective
  apply sub_eq_zero.mp
  apply hr
  rw [sub_mul]
  exact sub_eq_zero.mpr (by
    simpa only [hom_on_subopen,localMap] using hst)
end FramedLineMorphismContraction318
