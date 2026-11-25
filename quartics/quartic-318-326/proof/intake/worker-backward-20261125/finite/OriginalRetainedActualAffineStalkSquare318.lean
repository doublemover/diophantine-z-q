module

public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section
noncomputable section

namespace OriginalRetainedActualAffineStalkSquare318

open AlgebraicGeometry CategoryTheory

universe u
variable {B T : Type u} [CommRing B] [CommRing T]
/-- The actual prime stalk of the original affine, as a ring object.
An explicit abbreviation avoids syntax quotation around dependent projections. -/
abbrev affineStalk (B : Type u) [CommRing B]
    (z : Spec (CommRingCat.of B)) : CommRingCat.{u} :=
  (Spec (CommRingCat.of B)).presheaf.stalk z

variable {X : Scheme.{u}} (j : Spec (CommRingCat.of B) ⟶ X)
  [IsOpenImmersion j] (z : Spec (CommRingCat.of B))
variable (f : X ⟶ X) (fixed : f (j z)=j z)

def stalkChart : Spec (affineStalk B z) ⟶ X := (Spec (CommRingCat.of B)).fromSpecStalk z≫j

instance : Mono (stalkChart j z) := by
  unfold stalkChart
  infer_instance

theorem stalkChart_through_ambient :
    stalkChart j z=Spec.map (j.stalkMap z)≫X.fromSpecStalk (j z) :=
  (Scheme.SpecMap_stalkMap_fromSpecStalk j (x:=z)).symm

def samePointTransport : X.presheaf.stalk (j z) ⟶ X.presheaf.stalk (f (j z)) :=
  eqToHom (congrArg (fun x : X => X.presheaf.stalk x) fixed.symm)

instance : IsIso (samePointTransport j z f fixed) := by
  unfold samePointTransport
  infer_instance

theorem samePointTransport_read :
    Spec.map (samePointTransport j z f fixed)≫X.fromSpecStalk (j z) =
      X.fromSpecStalk (f (j z)) := by
  have t (x y : X) (h : x=y) :
      Spec.map (eqToHom (congrArg (fun r : X => X.presheaf.stalk r) h))≫
        X.fromSpecStalk x=X.fromSpecStalk y := by
    subst y
    simp
  exact t (j z) (f (j z)) fixed.symm

/-- The exact endomorphism of the old affine local ring induced by
the true Scheme map fixing the given origin. It is the actual stalk
map with the canonical open immersion and fixed-point transports. -/
def actualEnd : affineStalk B z ⟶ affineStalk B z :=
  inv (j.stalkMap z)≫samePointTransport j z f fixed≫f.stalkMap (j z)≫j.stalkMap z

theorem actualEnd_comp :
    Spec.map (actualEnd j z f fixed)≫stalkChart j z=stalkChart j z≫f := by
  let d := j.stalkMap z
  let t := samePointTransport j z f fixed
  let g := f.stalkMap (j z)
  have cancel : d≫actualEnd j z f fixed=(t≫g)≫d := by
    change d≫(inv d≫t≫g≫d)=(t≫g)≫d
    rw [IsIso.hom_inv_id_assoc,Category.assoc]
  rw [stalkChart_through_ambient j z]
  calc
    Spec.map (actualEnd j z f fixed)≫Spec.map d≫X.fromSpecStalk (j z)
        = Spec.map (d≫actualEnd j z f fixed)≫X.fromSpecStalk (j z) := by
          rw [Spec.map_comp,Category.assoc]
    _ = Spec.map d≫Spec.map g≫Spec.map t≫X.fromSpecStalk (j z) := by
          simp only [cancel,Spec.map_comp,Category.assoc]
    _ = Spec.map d≫Spec.map g≫X.fromSpecStalk (f (j z)) := by
          rw [show t=samePointTransport j z f fixed from rfl,samePointTransport_read]
    _ = (Spec.map d≫X.fromSpecStalk (j z))≫f := by
          rw [Category.assoc,←Scheme.SpecMap_stalkMap_fromSpecStalk f (x:=j z)]

theorem true_stalk_injective
    (inj : Function.Injective (actualEnd j z f fixed).hom) :
    Function.Injective (f.stalkMap (j z)).hom := by
  let d := j.stalkMap z
  let t := samePointTransport j z f fixed
  let g := f.stalkMap (j z)
  letI : IsIso d := inferInstanceAs (IsIso (j.stalkMap z))
  letI : IsIso t := inferInstanceAs (IsIso (samePointTransport j z f fixed))
  have compose : g=(inv t≫d)≫actualEnd j z f fixed≫inv d := by
    change g=(inv t≫d)≫(inv d≫t≫g≫d)≫inv d
    simp only [Category.assoc,IsIso.hom_inv_id_assoc,IsIso.inv_hom_id_assoc,
      IsIso.hom_inv_id,Category.comp_id]
  change Function.Injective g.hom
  rw [compose]
  exact (ConcreteCategory.bijective_of_isIso (inv d)).1.comp
    (inj.comp (ConcreteCategory.bijective_of_isIso (inv t≫d)).1)

variable (θ : B→+*T) (τ : affineStalk B z→+*T)
variable (readsBase : τ.comp (StructureSheaf.toStalk (CommRingCat.of B) z).hom=θ)

include readsBase in
theorem local_test_agrees :
    Spec.map (CommRingCat.ofHom τ)≫stalkChart j z=
      Spec.map (CommRingCat.ofHom θ)≫j := by
  let c : CommRingCat.of B ⟶ affineStalk B z :=
    StructureSheaf.toStalk (CommRingCat.of B) z
  have hstalk : (Spec (CommRingCat.of B)).fromSpecStalk z=Spec.map c :=
    Spec.fromSpecStalk_eq' (CommRingCat.of B) z
  have hread : c≫CommRingCat.ofHom τ=CommRingCat.ofHom θ :=
    congrArg (fun h : B→+*T => CommRingCat.ofHom h) readsBase
  calc
    _ = Spec.map (CommRingCat.ofHom τ)≫
        ((Spec (CommRingCat.of B)).fromSpecStalk z≫j) := rfl
    _ = Spec.map (CommRingCat.ofHom τ)≫(Spec.map c≫j) :=
      congrArg (fun h : Spec (affineStalk B z) ⟶ Spec (CommRingCat.of B) =>
        Spec.map (CommRingCat.ofHom τ)≫(h≫j)) hstalk
    _ = (Spec.map (CommRingCat.ofHom τ)≫Spec.map c)≫j :=
      (Category.assoc _ _ _).symm
    _ = Spec.map (c≫CommRingCat.ofHom τ)≫j :=
      congrArg (fun h : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of B) => h≫j)
        (Spec.map_comp c (CommRingCat.ofHom τ)).symm
    _ = _ := congrArg (fun h : CommRingCat.of B ⟶ CommRingCat.of T => Spec.map h≫j) hread

variable (nilMap : T→+*T)

include readsBase in
/-- Passage from equality of the genuine original affine thick test
arrows to equality on the original stalk uses the actual open chart
and natural Spec-stalk morphism. No independent local coframe or
stalk compatibility is postulated. -/
theorem whole_square_to_ring
    (square : (Spec.map (CommRingCat.ofHom θ)≫j)≫f=
      Spec.map (CommRingCat.ofHom (nilMap.comp θ))≫j) :
    τ.comp (actualEnd j z f fixed).hom=nilMap.comp τ := by
  have sq : Spec.map (CommRingCat.ofHom (τ.comp (actualEnd j z f fixed).hom))≫stalkChart j z=
      Spec.map (CommRingCat.ofHom (nilMap.comp τ))≫stalkChart j z := by
    let σ := stalkChart j z
    let qt := Spec.map (CommRingCat.ofHom τ)
    let q0 := Spec.map (CommRingCat.ofHom θ)
    let qp := Spec.map (CommRingCat.ofHom nilMap)
    calc
      Spec.map (CommRingCat.ofHom (τ.comp (actualEnd j z f fixed).hom))≫σ
          = qt≫(Spec.map (actualEnd j z f fixed)≫σ) := by
            change Spec.map (actualEnd j z f fixed≫CommRingCat.ofHom τ)≫σ=_
            rw [Spec.map_comp,Category.assoc]
      _ = (qt≫σ)≫f := by rw [actualEnd_comp j z f fixed,Category.assoc]
      _ = (q0≫j)≫f := by rw [local_test_agrees j z θ τ readsBase]
      _ = Spec.map (CommRingCat.ofHom (nilMap.comp θ))≫j := square
      _ = qp≫(q0≫j) := by
            change Spec.map (CommRingCat.ofHom θ≫CommRingCat.ofHom nilMap)≫j=_
            rw [Spec.map_comp,Category.assoc]
      _ = qp≫(qt≫σ) := by rw [local_test_agrees j z θ τ readsBase]
      _ = Spec.map (CommRingCat.ofHom (nilMap.comp τ))≫σ := by
            change _=Spec.map (CommRingCat.ofHom τ≫CommRingCat.ofHom nilMap)≫σ
            rw [Spec.map_comp,Category.assoc]
  have e := Spec.map_injective ((cancel_mono (stalkChart j z)).mp sq)
  exact congrArg (fun u : affineStalk B z ⟶ CommRingCat.of T => u.hom) e

end OriginalRetainedActualAffineStalkSquare318
