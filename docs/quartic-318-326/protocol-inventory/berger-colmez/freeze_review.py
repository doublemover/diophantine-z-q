#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
W=Path('/workspace/scratch/2cb21e4e0864');R=W/'diophantine-z-q';O=Path(__file__).parent
H=lambda x:hashlib.sha256(x).hexdigest()
v13=(R/'manuscripts/quartic_v13.tex').read_bytes();assert H(v13)=='9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd';lines=v13.splitlines(keepends=True)
passages=[]
for role,a,b in [('first_actual_representation',795,815),('first_monodromy',815,818),('first_Pan_consumer',832,844),('companion_representation_and_monodromy',7214,7230),('companion_Pan_consumer',7238,7246),('de_Rham_lemma',16472,16539),('Berger_bibliography',21749,21752)]:
 passages.append({'role':role,'path':'manuscripts/quartic_v13.tex','lines':[a,b],'excerpt_sha256':H(b''.join(lines[a-1:b]))})
assert passages[5]['excerpt_sha256']=='8f70f7912956fdf44c03ce33ed398527ec7151114d64619300fd06a628457e26'
sources=[{'id':'berger2002-author','url':'https://perso.ens-lyon.fr/laurent.berger/articles/article02.pdf','path':'private-sources/berger-author.pdf','status':'author format of published work; not final typeset comparison','locators':['section0.1 pages2–3','Theorem0.7 page6','Corollary5.22 page52'],'doi':'10.1007/s002220100202'}, {'id':'berger-errata','url':'https://perso.ens-lyon.fr/laurent.berger/articles/errata.pdf','path':'private-sources/berger-errata.pdf','status':'author errata dated2026-10-13','locators':['section1 pages1–2']}, {'id':'colmez2008-published','url':'https://numdam.org/item/AST_2008__319__117_0.pdf','path':'private-sources/colmez-published.pdf','status':'final published Numdam archival scan; exact equivalent monodromy theorem','locators':['section0.1 printed117–118','section0.2 and Theorem0.1 printed118']}]
for s in sources:s['sha256']=H((O/s['path']).read_bytes());s['bytes']=(O/s['path']).stat().st_size
assert sources[2]['bytes']==7343370
inputs={}
for p in ['v11-brinon-conrad-review/v13-carryforward.json','recovery-modular-0358/pan-v13-carry-forward/receipt.json','recovery-modular-0358/pan-v11-independent/sources/calegari-published.pdf','recovery-modular-0358/pan-v11-independent/excerpts/calegari-page624.txt']:
 inputs[p]=H((W/p).read_bytes())
assert inputs['v11-brinon-conrad-review/v13-carryforward.json']=='f08112f5939a2420a9ba5d87cd8a7daea32a999284e74375c4eefdc77333baa5'
assert inputs['recovery-modular-0358/pan-v13-carry-forward/receipt.json']=='b43c1c1d07d1f1a07ce1d53f8ec36af6cf1cd25ee888f82cfb6fd5dede576627'
(O/'SOURCES.json').write_text(json.dumps({'sources':sources,'published_Colmez_source_adoption_pending':True,'Berger_final_typeset_comparison':'incomplete; subscription route respected','correction_search_scope':'Berger author list and complete relevant errata section; Colmez exact-title errata/corrigendum search and author listing'},indent=2)+'\n')
(O/'BINDINGS.json').write_text(json.dumps({'v13_sha256':H(v13),'passages':passages,'adjacent_frozen_inputs':inputs,'source_reading_scope':'Primary statement, definitions and corrections; not full reproof of published theorems'},indent=2)+'\n')
report=(O/'REVIEW.md').read_text();assert all(f'{i}. **' in report for i in range(1,10))
receipt={'date':'2026-11-08','reviewer':'/root/restart_hodge_gluing','decision':'BOUNDED_LOCAL_APPLICATION_VALIDATED_AGAINST_PUBLISHED_EQUIVALENT_THEOREM; EXPLICIT_SOURCE_ADOPTION_PENDING','scope':'Actual V13 r_ell deRham-to-potentially-semistable local step, finite coefficient extension and Pan premise only','independent_of_target_manuscript_authorship':True,'nine_obligations':9,'v13_sha256':H(v13),'observed_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'files':{p:H((O/p).read_bytes()) for p in ['REVIEW.md','SOURCES.json','BINDINGS.json','freeze_review.py']},'remaining':['Berger author-to-final-typeset comparison not performed.','Explicitly add published Colmez Theorem0.1 as alternative/companion source if adopting this checked source route.','Independent consuming review and unchanged predecessor boundaries remain.'],'private_source_pdfs_excluded_from_public_archive':True,'shared_repo_edits':False,'lean_compilation':False}
(O/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS V13 and adjacent receipt hashes; all9obligations present; source PDF complete.')
print('receipt_sha256',H((O/'receipt.json').read_bytes()))
