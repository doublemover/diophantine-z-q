/-- Refined global realization obligation. This is deliberately not asserted:
actual geometry must supply each producer record and actual section/Hodge data.
The section field L, model field K, CM averaging degree and controlled isogeny
field degree remain distinct. -/
@[expose] def RefinedGeometricRealization : Prop := ∀u v:ℤ, IsCoprime u v →
    (∀j:Fin 5,ContactRadical318.forms u v j≠0) →
    (∃D:CMInputs u v, ∃(L:Type) (f:Field L) (nf:@NumberField L f),
      Nonempty (@MetricSections L f nf u v (D.surfaceHeight+Real.log Real.pi))) ∨
    ∃(K:Type) (f:Field K) (nf:@NumberField K f) (D:@NonCMInputs K f nf u v),
      ∃(L:Type) (lf:Field L) (lnf:@NumberField L lf),
        Nonempty (@MetricSections L lf lnf u v D.surfaceHeight)

theorem refined_implies_legacy (h:RefinedGeometricRealization) : GeometricRealization := by
  intro u v hc hn
  rcases h u v hc hn with hm | hnc
  · obtain ⟨D,L,f,nf,⟨S⟩⟩ := hm
    letI := f
    letI := nf
    exact Or.inl ⟨D.toLegacy S⟩
  · obtain ⟨K,f,nf,D,L,lf,lnf,⟨S⟩⟩ := hnc
    letI := f
    letI := nf
    letI := lf
    letI := lnf
    exact Or.inr ⟨K,f,nf,⟨D.toLegacy S⟩⟩

/-- Exact five-contact theorem from actual refined producer data; no final
contact/Jacobian/surface854R bound is a producer field. -/
theorem five_contact_of_refined_realization (h:RefinedGeometricRealization) :
    FiveContact49Height :=
  five_contact_of_realization (refined_implies_legacy h)

end RefinedContactRealization318
