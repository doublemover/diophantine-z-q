module
public import ContactProjectiveQuotientParameter318
public section
noncomputable section
namespace ContactProjectiveParameterStructure318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (n : ℕ)
/-- The rational structure descends with the actual parameter chart
maps, rather than being imposed on a detached glued space. -/
@[expose] def structureMap : ContactProjectiveQuotientParameter318.scheme c n ⟶ Spec (CommRingCat.of ℚ) := by
  fapply Multicoequalizer.desc
  · exact fun a => VaryingWordParameterStructure318.structureMap ℚ (ring c a) (Fin n)
  rintro ⟨a,b⟩
  change (parameterOpen c a b n).ι ≫ VaryingWordParameterStructure318.structureMap ℚ (ring c a) (Fin n)=
    ((ContactQuotientOverlapSchemeIso318.iso c a b n).hom ≫ (parameterOpen c b a n).ι) ≫
      VaryingWordParameterStructure318.structureMap ℚ (ring c b) (Fin n)
  rw [Category.assoc]
  exact (ContactQuotientOverlapSchemeIso318.over c a b n).symm
@[reassoc] lemma into_structureMap (a : Chart) : ContactProjectiveQuotientParameter318.into c n a ≫
    structureMap c n=VaryingWordParameterStructure318.structureMap ℚ (ring c a) (Fin n) :=
  Multicoequalizer.π_desc _ _ _ _ _
end ContactProjectiveParameterStructure318
