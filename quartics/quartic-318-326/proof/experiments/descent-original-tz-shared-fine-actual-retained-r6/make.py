from pathlib import Path
base=Path('tz-hybrid-retained-mellin-publication-r12/descent-original-tz-hybrid-retained-mellin-r12')
p=Path('ray-tz-shared-fine-context-r1')
s=(base/'ActualTZHybridCanonicalWrap318.lean').read_text()
s=s.replace('ActualTZHybridCanonicalWrap318','ActualTZSharedFineCanonicalWrap318')
s=s.replace('ActualTZHybridGrid318','ActualTZSharedFineHybridGrid318')
s=s.replace('ActualTZHybridGlobalLocalStencil318','ActualTZSharedFineHybridStencil318')
s=s.replace('variable {a t s : ℕ}','variable {a t b s : ℕ}')
s=s.replace('Context (a t s : ℕ)', 'Context (a t b s : ℕ)')
s=s.replace('Context a t s I','Context a t b s I')
s=s.replace('  b : ℕ','  residueClass : ℕ').replace('1≤b ∧ b≤primorial y ∧ (primorial y).Coprime b',
  '1≤residueClass ∧ residueClass≤primorial y ∧ (primorial y).Coprime residueClass')
s=s.replace('L.b','L.residueClass')
s=s.replace('divided : Fin s→ℤ','divided : Fin b→Fin s→ℤ')
s=s.replace('divided_bound : ∀ j,(divided j).natAbs≤D','divided_bound : ∀ j k,(divided j k).natAbs≤D')
s=s.replace('divided_ne : ∃ j,divided j≠0','divided_ne : ∀ j,∃ k,divided j k≠0')
s=s.replace('Bits a t','Bits a t b')
s=s.replace('a+2*t*s*','a+2*t*b*s*')
s=s.replace('GridOf a t s','GridOf a t b s').replace('lengths a t s','lengths a t b s')
s=s.replace('starts a t s','starts a t b s').replace('Vals a t s','Vals a t b s')
s=s.replace('flat a t s','flat a t b s').replace('Poly a t s','Poly a t b s')
s=s.replace('dim a t s','dim a t b s').replace('Coord a t s','Coord a t b s')
s=s.replace('def actualSlope (i : Fin s) : ℤ := (primorial L.y:ℤ)*L.divided i',
  'def actualSlope (j : Fin b) (k : Fin s) : ℤ := (primorial L.y:ℤ)*L.divided j k')
s=s.replace('  apply off_bound _ _ _ L.J L.M (primorial L.y) L.q L.n L.D L.C L.global_small L.local_small',
  '  apply ActualTZSharedFineHybridOffsetCap318.off_bound a t b s L.J L.M (primorial L.y) L.q L.n L.D L.C\n    L.global_small L.local_small')
s=s.replace('  · intro j\n    unfold actualSlope','  · intro j k\n    unfold actualSlope')
s=s.replace('L.divided_bound j','L.divided_bound j k')
s=s.replace('  · intro r\n    have hx (b : Bool)', '  · intro r j\n    have hx (e : Bool)')
s=s.replace('L.pt z (.inr (r,.inr b))','L.pt z (.inr (r,.inr (j,e)))')
s=s.replace('unflat z (.inr (r,.inr b))','unflat z (.inr (r,.inr (j,e)))')
s=s.replace('  obtain ⟨j,hj⟩ := L.divided_ne\n  have h := survives (primorial L.y) L.n L.q p L.D hp (L.cut.trans_lt hY) hP L.divided j\n    hj (L.divided_bound j k) (L.site i.val.1) (L.site i.val.2)',
  '  have hRow (j : Fin b) : ∃ k,L.divided j k≠0 ∧ (L.divided j k).natAbs≤L.D := by\n    obtain ⟨k,hk⟩ := L.divided_ne j\n    exact ⟨k,hk,L.divided_bound j k⟩\n  have h := ActualTZSharedFinePrimeMarker318.survives (primorial L.y) L.n L.q p L.D hp\n    (L.cut.trans_lt hY) hP L.divided hRow (L.site i.val.1) (L.site i.val.2)')
s=s.replace('L.actualSlope=(fun j : Fin s=>(primorial L.y:ℤ)*L.divided j)',
  'L.actualSlope=(fun (j : Fin b) (k : Fin s)=>(primorial L.y:ℤ)*L.divided j k)')
s=s.replace('      funext j\n      rfl','      funext j k\n      rfl')
assert 'obtain ⟨j,hj⟩' not in s and 'L.divided j)' not in s
s=s.replace('/-- Literal off-grid local and global test. Explicitly different\ncoordinate widths; a single canonical cyclic x is shared by the\nwhole mask. Fixed D,C do not depend on the model cutoff. -/',
  '/-- Genuine multi-axis local/global test: one fine table per local block,\none single canonical cyclic x, with width J on global endpoints, M on the\nfine table and 2*M+1 on every local endpoint. Fixed D,C are cutoff-independent. -/')
(p/'ActualTZSharedFineCanonicalWrap318.lean').write_text(s)
for short in ('MeanCell','MeanAverage'):
 old=(base/f'ActualTZHybrid{short}318.lean').read_text()
 for label in ('CanonicalWrap','MeanCell','MeanAverage'):
  old=old.replace(f'ActualTZHybrid{label}318',f'ActualTZSharedFine{label}318')
 old=old.replace('ActualTZHybridGrid318','ActualTZSharedFineHybridGrid318')
 old=old.replace('{a t s : ℕ}','{a t b s : ℕ}').replace('Context a t s I','Context a t b s I')
 old=old.replace('dim a t s','dim a t b s')
 (p/f'ActualTZSharedFine{short}318.lean').write_text(old)
old=(base/'ActualTZHybridMaskMean318.lean').read_text()
old=old[:old.index('/-- One finite-exhaustion threshold')]+ 'end ActualTZHybridMaskMean318\n'
for label in ('CanonicalWrap','MeanCell','MeanAverage','MaskMean'):
 old=old.replace(f'ActualTZHybrid{label}318',f'ActualTZSharedFine{label}318')
old=old.replace('ActualTZHybridGlobalLocalStencil318','ActualTZSharedFineHybridStencil318')
old=old.replace('ActualTZHybridGrid318','ActualTZSharedFineHybridGrid318')
old=old.replace('ActualTZHybridOrderedMeaning318','ActualTZSharedFineHybridOrdered318')
old=old.replace('public import ActualTZHybridMeanRate318','public import ActualTZSharedFineMeanAverage318')
old=old.replace('public import ActualTZSharedFineHybridOrdered318','public import ActualTZSharedFineHybridOrdered318\npublic import ActualTZOneAxisLocalDual318')
old=old.replace('public import ActualTZFiniteCutoffUniformity318\n','').replace(
 'open ActualTZHybridMeanRate318\n','').replace(
 'open ActualTZLiteralSchwartz318 ActualTZLiteralOrdinaryBound318 ActualTZOneDivisorExpansion318',
 'open ActualTZOneDivisorExpansion318')
old=old.replace('{a t s : ℕ}','{a t b s : ℕ}').replace('Context a t s','Context a t b s')
old=old.replace('Bits a t','Bits a t b').replace('Ordered a t s','Ordered a t b s')
old=old.replace('orderedEquiv a t s','orderedEquiv a t b s')
old=old.replace('  b := X.b','  residueClass := X.residueClass').replace('+X.b)', '+X.residueClass)')
old=old.replace('exactShift','shift')
old=old.replace('import all ActualTZSharedFineMeanAverage318','import all ActualTZSharedFineCanonicalWrap318\nimport all ActualTZSharedFineMeanAverage318')
(p/'ActualTZSharedFineMaskMean318.lean').write_text(old)
