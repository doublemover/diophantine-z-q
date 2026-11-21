module
public import ActualGaussianResidueOrbit318
public section
noncomputable section
namespace ActualLinearQGaussianResidueCoordinates318

open ActualGaussianResidueOrbit318
open Classical

@[expose] def coordinate (M : ℕ) (z : GaussianInt) : ZMod M × ZMod M :=
  ((z.re:ZMod M),(z.im:ZMod M))

/-- The converse of the earlier source's congruence projection:
Gaussian ideal congruence is equivalent to BOTH integer congruences.
No field or prime condition is used at this exact scalar modulus. -/
theorem red_eq_iff_coordinates (M : ℕ) (z w : GaussianInt) :
    red M z=red M w ↔ coordinate M z=coordinate M w := by
  constructor
  · intro h
    have h' := full_coordinate_congruence (M:=M) h
    exact Prod.ext ((ZMod.intCast_eq_intCast_iff _ _ M).mpr h'.1)
      ((ZMod.intCast_eq_intCast_iff _ _ M).mpr h'.2)
  · intro h
    have hre := (ZMod.intCast_eq_intCast_iff z.re w.re M).mp (congrArg Prod.fst h)
    have him := (ZMod.intCast_eq_intCast_iff z.im w.im M).mp (congrArg Prod.snd h)
    obtain ⟨a,ha⟩ := hre.dvd
    obtain ⟨b,hb⟩ := him.dvd
    apply (Ideal.Quotient.eq (I:=modIdeal M)).mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(⟨-a,-b⟩:GaussianInt),?_⟩
    apply Zsqrtd.ext
    · simp only [Zsqrtd.re_sub,Zsqrtd.re_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast,
        zero_mul,zero_add,mul_zero,add_zero]
      change z.re-w.re=(M:ℤ)*(-a)
      linear_combination -ha
    · simp only [Zsqrtd.im_sub,Zsqrtd.im_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast,
        zero_mul,zero_add,mul_zero,add_zero]
      change z.im-w.im=(M:ℤ)*(-b)
      linear_combination -hb

@[expose] def representative (M : ℕ) (x : ZMod M × ZMod M) : GaussianInt :=
  ⟨ZMod.cast x.1,ZMod.cast x.2⟩

theorem coordinate_representative (M : ℕ) (x : ZMod M × ZMod M) :
    coordinate M (representative M x)=x := by
  exact Prod.ext (ZMod.intCast_zmod_cast x.1) (ZMod.intCast_zmod_cast x.2)

@[expose] def fromPair (M : ℕ) (x : ZMod M × ZMod M) : Residue M :=
  red M (representative M x)

/-- Quotient-by-(M) Gaussian residues, not merely representatives
chosen at rational prime norms. Works at composite modulus and at M=1. -/
def equiv (M : ℕ) : (ZMod M × ZMod M) ≃ Residue M :=
  Equiv.ofBijective (fromPair M) (by
    constructor
    · intro x y e
      change red M (representative M x)=red M (representative M y) at e
      have ee := (red_eq_iff_coordinates M _ _).mp e
      rwa [coordinate_representative,coordinate_representative] at ee
    · intro z
      obtain ⟨z',h⟩ := Ideal.Quotient.mk_surjective z
      change red M z'=z at h
      refine ⟨coordinate M z',?_⟩
      change red M (representative M (coordinate M z'))=z
      rw [←h,red_eq_iff_coordinates,coordinate_representative])

theorem equiv_pair (M : ℕ) (x : ZMod M × ZMod M) : equiv M x=fromPair M x := rfl

theorem equiv_coord (M : ℕ) (z : GaussianInt) :
    (equiv M).symm (red M z)=coordinate M z := by
  apply (equiv M).injective
  rw [Equiv.apply_symm_apply,equiv_pair,fromPair,red_eq_iff_coordinates,coordinate_representative]

theorem project_zero (M : ℕ) : (equiv M).symm 0=(0,0) := by
  rw [←(red M).map_zero,equiv_coord] <;> simp [coordinate]

theorem project_one (M : ℕ) : (equiv M).symm 1=(1,0) := by
  rw [←(red M).map_one,equiv_coord] <;> simp [coordinate]

theorem project_add (M : ℕ) (x y : Residue M) :
    (equiv M).symm (x+y)=
      (((equiv M).symm x).1+((equiv M).symm y).1,
        ((equiv M).symm x).2+((equiv M).symm y).2) := by
  obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective y
  change red M a=x at ha
  change red M b=y at hb
  rw [←ha,←hb,←map_add,equiv_coord,equiv_coord,equiv_coord]
  simp only [coordinate,Zsqrtd.re_add,Zsqrtd.im_add,Int.cast_add]

theorem project_mul (M : ℕ) (x y : Residue M) :
    let a := (equiv M).symm x
    let b := (equiv M).symm y
    (equiv M).symm (x*y)=(a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1) := by
  dsimp only
  obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective y
  change red M a=x at ha
  change red M b=y at hb
  rw [←ha,←hb,←map_mul,equiv_coord,equiv_coord,equiv_coord]
  simp only [coordinate,Zsqrtd.re_mul,Zsqrtd.im_mul,Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_one,
    Prod.fst,Prod.snd]
  congr 1 <;> ring

/-- Coordinatewise scalar-ring specialization induces a genuine
Gaussian residue ring homomorphism. In particular this turns all
scalar CRT projections into the actual Gaussian quotient maps. -/
def pairMap {M d : ℕ} (f : ZMod M →+* ZMod d) : Residue M →+* Residue d where
  toFun x := fromPair d (f (((equiv M).symm x).1),f (((equiv M).symm x).2))
  map_zero' := by
    apply (equiv d).symm.injective
    simp only [project_zero,←equiv_pair,Equiv.symm_apply_apply,Prod.fst,Prod.snd,map_zero]
  map_one' := by
    apply (equiv d).symm.injective
    simp only [project_one,←equiv_pair,Equiv.symm_apply_apply,Prod.fst,Prod.snd,map_one,map_zero]
  map_add' x y := by
    apply (equiv d).symm.injective
    simp only [project_add,←equiv_pair,Equiv.symm_apply_apply,Prod.fst,Prod.snd,map_add]
  map_mul' x y := by
    apply (equiv d).symm.injective
    simp only [project_mul,←equiv_pair,Equiv.symm_apply_apply,Prod.fst,Prod.snd,map_mul,map_sub,map_add]

theorem project_pairMap {M d : ℕ} (f : ZMod M →+* ZMod d) (x : Residue M) :
    (equiv d).symm (pairMap f x)=
      (f (((equiv M).symm x).1),f (((equiv M).symm x).2)) := by
  change (equiv d).symm (fromPair d _)=_
  rw [←equiv_pair,Equiv.symm_apply_apply]

theorem pairMap_castHom {M d : ℕ} (h : d ∣ M) (z : GaussianInt) :
    pairMap (ZMod.castHom h (ZMod d)) (red M z)=red d z := by
  apply (equiv d).symm.injective
  rw [project_pairMap,equiv_coord,equiv_coord]
  simp only [coordinate,Prod.fst,Prod.snd,map_intCast]

@[expose] def norm (M : ℕ) (u : Residue M) : ZMod M :=
  ((equiv M).symm u).1^2+((equiv M).symm u).2^2

theorem norm_fromPair (M : ℕ) (z : ZMod M × ZMod M) :
    norm M (fromPair M z)=z.1^2+z.2^2 := by
  rw [norm,←equiv_pair,Equiv.symm_apply_apply]

theorem norm_red (M : ℕ) (z : GaussianInt) : norm M (red M z)=(z.norm:ZMod M) := by
  rw [norm,equiv_coord,norm_coords]
  simp only [coordinate,coords,Prod.fst,Prod.snd,Int.cast_add,Int.cast_pow]

/-- Norm on the actual Gaussian quotient; arithmetic, not a
Frobenius homomorphism. -/
def normHom (M : ℕ) : Residue M →* ZMod M where
  toFun := norm M
  map_one' := by
    change norm M (1:Residue M)=1
    rw [←(red M).map_one,norm_red,norm_coords] <;> norm_num [coords]
  map_mul' x y := by
    change norm M (x*y)=norm M x*norm M y
    obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective y
    change red M a=x at ha
    change red M b=y at hb
    rw [←ha,←hb,←map_mul,norm_red,norm_red,norm_red,Zsqrtd.norm_mul,Int.cast_mul]

theorem normHom_apply (M : ℕ) (x : Residue M) : normHom M x=norm M x := rfl

theorem isUnit_iff_norm_unit (M : ℕ) (x : Residue M) :
    IsUnit x ↔ IsUnit (norm M x) := by
  constructor
  · intro h
    rw [←normHom_apply]
    exact h.map (normHom M)
  · intro h
    obtain ⟨z,hz⟩ := Ideal.Quotient.mk_surjective x
    change red M z=x at hz
    rw [←hz,norm_red] at h
    have hCast : (z.norm:ZMod M)=(z.norm.natAbs:ZMod M) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun k : ℤ => (k:ZMod M)) (GaussianInt.abs_natCast_norm z).symm
    rw [hCast] at h
    rw [←hz]
    exact unit_of_norm_coprime M z ((ZMod.isUnit_iff_coprime z.norm.natAbs M).mp h)

end ActualLinearQGaussianResidueCoordinates318
