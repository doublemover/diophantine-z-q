module
public import OriginalR47PointedSiteActualAffine318
public import OriginalR47PointedReesAlignment318
public section
noncomputable section

namespace OriginalR47ActualPointedRound318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalThickCentralReesChart318 (O I)
open OriginalR47PointedReesAlignment318 (Aligned extended asSpec)
open OriginalAffineReesBlowup318 (blowup projection)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type} [CommRing R] [CommRing A]
variable (q : R) (d : ℕ) (p : Ideal A) [p.IsMaximal]

variable {X U : Scheme} (e : U ⟶ X) (l : U ⟶ Spec (CommRingCat.of (O q d)))
variable (j : Spec (CommRingCat.of A) ⟶ X) (u₀ : U)

structure Actual where
  V : OriginalR47PointedSiteActualAffine318.Chart e l j u₀ (⟨p,inferInstance⟩ : PrimeSpectrum A)
  alignment :
    letI : Algebra A V.B := V.old.hom.toAlgebra
    letI : Algebra (O q d) V.B := V.split.hom.toAlgebra
    Aligned q d p V.point

/-- Real pointed glue: use the given two pointed étale arrows into the
existing old scheme and the actual literal node, and the given original
affine centre. Even the common affine ring is chosen from these arrows
rather than introduced as a second model. -/
theorem of_site [IsOpenImmersion j]
    [Flat e] [FormallyUnramified e] [LocallyOfFiniteType e]
    [Flat l] [FormallyUnramified l] [LocallyOfFiniteType l]
    [ (OriginalR47LiteralNodeCentre318.uniformizerIdeal q).IsMaximal ]
    (hp : e u₀ = j ⟨p,inferInstance⟩)
    (hs : (l u₀).asIdeal = I q d) :
    Nonempty (Actual q d p e l j u₀) := by
  obtain ⟨V⟩ := OriginalR47PointedSiteActualAffine318.choose
    e l j u₀ (⟨p,inferInstance⟩ : PrimeSpectrum A) hp
  let : Algebra A V.B := V.old.hom.toAlgebra
  let : Algebra (O q d) V.B := V.split.hom.toAlgebra
  let : Module.Flat A V.B := RingHom.flat_algebraMap_iff.mp V.old_flat
  let : Module.Flat (O q d) V.B := RingHom.flat_algebraMap_iff.mp V.split_flat
  let : Algebra.FormallyUnramified A V.B :=
    RingHom.formallyUnramified_algebraMap.mp V.old_unram
  let : Algebra.FormallyUnramified (O q d) V.B :=
    RingHom.formallyUnramified_algebraMap.mp V.split_unram
  let : Algebra.FiniteType A V.B := RingHom.finiteType_algebraMap.mp V.old_finite
  let : Algebra.FiniteType (O q d) V.B := RingHom.finiteType_algebraMap.mp V.split_finite
  have hp' : PrimeSpectrum.comap (algebraMap A V.B) V.point = ⟨p,inferInstance⟩ :=
    V.old_read
  have hs' : (PrimeSpectrum.comap (algebraMap (O q d) V.B) V.point).asIdeal = I q d :=
    (congrArg PrimeSpectrum.asIdeal V.split_read).trans hs
  obtain ⟨Z⟩ := OriginalR47PointedReesAlignment318.align q d p V.point hp' hs'
  exact ⟨⟨V,Z⟩⟩

/-- The genuine R47 input uses the DVR uniformizer already present in
its pointed split-node site. Its closed-centre maximality is derived. -/
theorem of_dvr_site [IsDomain R] [IsDiscreteValuationRing R] (hq : Irreducible q)
    [IsOpenImmersion j]
    [Flat e] [FormallyUnramified e] [LocallyOfFiniteType e]
    [Flat l] [FormallyUnramified l] [LocallyOfFiniteType l]
    (hp : e u₀ = j ⟨p,inferInstance⟩)
    (hs : (l u₀).asIdeal = I q d) :
    Nonempty (Actual q d p e l j u₀) := by
  let := OriginalR47LiteralNodeCentre318.uniformizer_maximal q hq
  exact of_site q d p e l j u₀ hp hs

/-- Paste the common point-aligned blowup to the given genuine old
affine chart of the *actual* round, rather than producing a new round. -/
theorem to_actual_round {Y : Scheme} (r : Y ⟶ X) (i : blowup p ⟶ Y)
    (h : IsPullback i (projection p) r j) (M : Actual q d p e l j u₀) :
    letI : Algebra A M.V.B := M.V.old.hom.toAlgebra
    letI : Algebra (O q d) M.V.B := M.V.split.hom.toAlgebra
    let F := M.alignment
    IsPullback (F.toOld ≫ i) (projection F.W.point.asIdeal) r
      (asSpec (extended (A:=A) F.W.g) ≫ j) := by
  dsimp only
  let : Algebra A M.V.B := M.V.old.hom.toAlgebra
  let : Algebra (O q d) M.V.B := M.V.split.hom.toAlgebra
  let F : Aligned q d p M.V.point := M.alignment
  exact F.oldSquare.paste_horiz h

end OriginalR47ActualPointedRound318

#print axioms OriginalR47ActualPointedRound318.of_site
#print axioms OriginalR47ActualPointedRound318.of_dvr_site
#print axioms OriginalR47ActualPointedRound318.to_actual_round
