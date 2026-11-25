module
public import OriginalR47LiteralNodeCentre318
public import OriginalR47PointedCommonCentre318
public import OriginalR47ReesProjFlat318
public import OriginalUpperReesFibreTransfer318
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat
public section
noncomputable section

namespace OriginalR47PointedReesAlignment318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PrimeSpectrum
open OriginalR47PointedCommonCentre318
open OriginalAffineReesBlowup318
open OriginalThickCentralReesChart318 (O I)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ring map of the actual common affine localization, before passing to Spec. -/
abbrev extended {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : B) :
    A →+* Localization.Away g := (further g).comp (algebraMap A B)

abbrev asSpec {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :=
  Spec.map (CommRingCat.ofHom f)

variable {A R B : Type} [CommRing A] [CommRing R] [CommRing B]
variable [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (d : ℕ) (p : Ideal A) [p.IsMaximal]
variable [Algebra A B] [Algebra (O q d) B]

/-- The old and split arrows are given by the two actual ring maps of
one common affine site. Both new Rees maps start at the blowup of the
same actual point ideal in the single chosen affine localization. -/
structure Aligned (u₀ : PrimeSpectrum B) where
  [splitMax : (I q d).IsMaximal]
  W : Window p (I q d) u₀
  toOld : blowup W.point.asIdeal ⟶ blowup p
  toSplit : blowup W.point.asIdeal ⟶ blowup (I q d)
  oldSquare : IsPullback toOld (projection W.point.asIdeal) (projection p)
    (asSpec (extended (A:=A) W.g))
  splitSquare : IsPullback toSplit (projection W.point.asIdeal) (projection (I q d))
    (asSpec (extended (A:=O q d) W.g))
  oldRead : asSpec (extended (A:=A) W.g) W.point = ⟨p,inferInstance⟩
  splitRead : (asSpec (extended (A:=O q d) W.g) W.point).asIdeal = I q d

private theorem lift_flat {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
    [Module.Flat S T] (g : T) : (extended (A:=S) g).Flat := by
  have h₁ : (algebraMap S T).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h₂ : (further g).Flat := RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (Localization.Away g) (Submonoid.powers g))
  exact RingHom.Flat.comp h₁ h₂

/-- Keep the target ring abstract while applying the strict flat Rees
comparison; the flat module is the one from the exact ring map. In
particular no default Ore module is synthesized on the later concrete
principal localization. -/
private theorem cartesian_of_flat {S D : Type} [CommRing S] [CommRing D]
    (I₀ : Ideal S) {ι : Type} (a : ι → I₀)
    (hspan : Ideal.span (Set.range (fun i => (a i).val)) = I₀)
    (f : S →+* D) (hf : f.Flat) :
    ∃ j : blowup (I₀.map f) ⟶ blowup I₀,
      IsPullback j (projection (I₀.map f)) (projection I₀) (asSpec f) := by
  let : Algebra S D := f.toAlgebra
  let : Module.Flat S D := RingHom.flat_algebraMap_iff.mp
    (show (algebraMap S D).Flat from hf)
  exact ⟨_,OriginalR47ReesProjFlat318.cartesian (B:=D) I₀ a hspan⟩

omit [IsDomain R] [UniqueFactorizationMonoid R] in
/-- Construct the pointed comparison on the actual split node O(q,d)
and the actual original affine centre p, with the three literal split
generators x,y,q used in the R40 atlas. No common ideal is assumed. -/
theorem align (u₀ : PrimeSpectrum B)
    [ (OriginalR47LiteralNodeCentre318.uniformizerIdeal q).IsMaximal ]
    [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B] [Module.Flat A B]
    [Algebra.EssFiniteType (O q d) B] [Algebra.FormallyUnramified (O q d) B]
    [Module.Flat (O q d) B]
    (hp : comap (algebraMap A B) u₀ = ⟨p,inferInstance⟩)
    (hs : (comap (algebraMap (O q d) B) u₀).asIdeal = I q d) :
    Nonempty (Aligned q d p u₀) := by
  let : (I q d).IsMaximal := OriginalR47LiteralNodeCentre318.maximal q d
  have hs' : comap (algebraMap (O q d) B) u₀ = ⟨I q d,inferInstance⟩ :=
    PrimeSpectrum.ext hs
  obtain ⟨W⟩ := window p (I q d) u₀ hp hs'
  have hI := same_closed_centre p (I q d) u₀ W
  have oldEq : p.map (extended (A:=A) W.g) = W.point.asIdeal := by
    rw [extended, ← Ideal.map_map]
    exact hI.1
  have splitEq : (I q d).map (extended (A:=O q d) W.g) = W.point.asIdeal := by
    rw [extended, ← Ideal.map_map]
    exact hI.2
  have pgen : Ideal.span (Set.range (fun x : p => x.val)) = p := by
    have H : Set.range (fun x : p => x.val) = (p : Set A) := by
      ext x
      exact ⟨fun ⟨z,hz⟩ => hz ▸ z.property, fun h => ⟨⟨x,h⟩,rfl⟩⟩
    rw [H, Ideal.span_eq]
  have hOld : ∃ F : blowup W.point.asIdeal ⟶ blowup p,
      IsPullback F (projection W.point.asIdeal) (projection p)
        (asSpec (extended (A:=A) W.g)) := by
    rw [← oldEq]
    exact cartesian_of_flat p id pgen (extended (A:=A) W.g) (lift_flat (S:=A) W.g)
  have hSplit : ∃ F : blowup W.point.asIdeal ⟶ blowup (I q d),
      IsPullback F (projection W.point.asIdeal) (projection (I q d))
        (asSpec (extended (A:=O q d) W.g)) := by
    rw [← splitEq]
    exact cartesian_of_flat (I q d)
      (OriginalLiteralThickNodeReesAtlas318.select q d)
      (OriginalLiteralThickNodeReesAtlas318.selected q d)
      (extended (A:=O q d) W.g) (lift_flat (S:=O q d) W.g)
  obtain ⟨F,hF⟩ := hOld
  obtain ⟨G,hG⟩ := hSplit
  have hOldRead : asSpec (extended (A:=A) W.g) W.point = ⟨p,inferInstance⟩ := by
    change comap (algebraMap A B) (comap (further W.g) W.point) = _
    rw [W.read,hp]
  have hSplitRead : (asSpec (extended (A:=O q d) W.g) W.point).asIdeal = I q d := by
    change (comap (algebraMap (O q d) B) (comap (further W.g) W.point)).asIdeal = _
    rw [W.read,hs]
  exact ⟨{
    splitMax := inferInstance
    W := W
    toOld := F
    toSplit := G
    oldSquare := hF
    splitSquare := hG
    oldRead := hOldRead
    splitRead := hSplitRead
  }⟩

/-- Although the original étale site need not have singleton fibre,
the one restricted marked point suffices to lift every point of the
actual old blowup fibre, by the genuine Cartesian square. Every lift
is then in one of the three exact central/thin outer R40 charts. -/
theorem covers_old_fibre {u₀ : PrimeSpectrum B} (F : Aligned q d p u₀)
    (hq : Irreducible q) (z : blowup p) (hz : projection p z = ⟨p,inferInstance⟩) :
    ∃ v : blowup F.W.point.asIdeal, F.toOld v = z ∧
      projection F.W.point.asIdeal v = F.W.point ∧
      (F.toSplit v ∈ Set.range (OriginalLiteralThickNodeReesAtlas318.central q d hq.ne_zero) ∨
        ∃ b : Bool, F.toSplit v ∈ Set.range
          (OriginalLiteralThickNodeReesAtlas318.outer q d hq.ne_zero b)) := by
  obtain ⟨v,hv,hr⟩ := Scheme.exists_preimage_of_isPullback F.oldSquare z F.W.point
      (hz.trans F.oldRead.symm)
  exact ⟨v,hv,hr,OriginalLiteralThickNodeReesAtlas318.covers q d hq.ne_zero (F.toSplit v)⟩

theorem connected_common_fibre {u₀ : PrimeSpectrum B} (F : Aligned q d p u₀)
    (hq : Irreducible q) :
    _root_.IsConnected (projection F.W.point.asIdeal ⁻¹' ({F.W.point} : Set _)) :=
  OriginalUpperReesFibreTransfer318.split_connected_in_square q hq d
    F.splitSquare F.W.point F.splitRead

end OriginalR47PointedReesAlignment318

#print axioms OriginalR47PointedReesAlignment318.align
#print axioms OriginalR47PointedReesAlignment318.covers_old_fibre
#print axioms OriginalR47PointedReesAlignment318.connected_common_fibre
