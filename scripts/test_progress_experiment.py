"""Fail-closed source/cache admission and isolated experiment regression tests."""
import copy
import json
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_progress_experiment as e
import check_progress_lean as ci

class ExperimentTests(unittest.TestCase):
    def fixture(self,root):
        p=root/'sample';p.mkdir()
        (p/'Draft.lean').write_text('module\npublic import Base\npublic def answer : Nat := 42\n')
        d={'order':['Draft'],'files':{'Draft.lean':{'sha256':ci.sha(p/'Draft.lean'),'imports':['Base']}}}
        ci.write_json(p/'intake.json',d)
        plan={'module_order':['A','Base','Unused'],'module_keys':{'A':'a','Base':'b','Unused':'u'},
              'dependencies':{'A':[],'Base':['A'],'Unused':[]},'base':'base'}
        return p,d,plan
    def test_valid_packet_and_only_required_closure(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p,d,plan=self.fixture(root)
            _,_,direct,ext=e.packet('sample',plan,root)
            self.assertEqual(e.required_baseline(plan,direct),['A','Base']);self.assertFalse(ext)
    def test_application_evidence_bindings_fail_closed(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p,d,plan=self.fixture(root)
            evidence=p/'SOURCE_SHA256SUMS';evidence.write_text('exact source list\n')
            digest=ci.sha(evidence)
            ci.write_json(p/'APPLICATION.json',{'bindings':{'SOURCE_SHA256SUMS':digest}})
            e.packet('sample',plan,root)
            evidence.write_text('stale source list\n')
            with self.assertRaisesRegex(ValueError,'evidence hash mismatch'):
                e.packet('sample',plan,root)
            evidence.unlink()
            with self.assertRaisesRegex(ValueError,'Missing application evidence'):
                e.packet('sample',plan,root)
            for bindings in [{'../outside':digest},{'SOURCE_SHA256SUMS':'not-a-digest'},[]]:
                ci.write_json(p/'APPLICATION.json',{'bindings':bindings})
                with self.assertRaisesRegex(ValueError,'Invalid application'):
                    e.packet('sample',plan,root)

    def test_ignored_application_evidence_must_be_published(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p,d,plan=self.fixture(root)
            subprocess.run(['git','init','-q',str(root)],check=True)
            (root/'.gitignore').write_text('*.log\n')
            evidence=p/'hosted-evidence.log';evidence.write_text('original hosted bytes\n')
            ci.write_json(p/'APPLICATION.json',{'bindings':{'hosted-evidence.log':ci.sha(evidence)}})
            e.packet('sample',plan,root)  # Local presence and the exact hash alone pass.
            with self.assertRaisesRegex(ValueError,'not tracked in Git'):
                e.check_application_publication([p],root)
            subprocess.run(['git','-C',str(root),'add','-f','sample/hosted-evidence.log'],check=True)
            e.check_application_publication([p],root)
            subprocess.run(['git','-C',str(root),'rm','--cached','sample/hosted-evidence.log'],
                           check=True,stdout=subprocess.DEVNULL)
            self.assertTrue(evidence.is_file())
            with self.assertRaisesRegex(ValueError,'not tracked in Git'):
                e.check_application_publication([p],root)

    def test_source_mutation_and_declared_imports_fail(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p,d,plan=self.fixture(root)
            (p/'Draft.lean').write_text('module\npublic import Unknown\n')
            with self.assertRaisesRegex(ValueError,'hash'):e.packet('sample',plan,root)
            d['files']['Draft.lean']['sha256']=ci.sha(p/'Draft.lean');ci.write_json(p/'intake.json',d)
            with self.assertRaisesRegex(ValueError,'imports'):e.packet('sample',plan,root)
            d['files']['Draft.lean']['imports']=['Unknown'];ci.write_json(p/'intake.json',d)
            with self.assertRaisesRegex(ValueError,'Unknown'):e.packet('sample',plan,root)
    def test_shadowing_duplicate_and_path_names_fail(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p,d,plan=self.fixture(root)
            with self.assertRaises(ValueError):e.packet('../sample',plan,root)
            plan['module_keys']['Draft']='x'
            with self.assertRaisesRegex(ValueError,'shadowing'):e.packet('sample',plan,root)
            d['order']=['Draft','Draft'];ci.write_json(p/'intake.json',d)
            with self.assertRaisesRegex(ValueError,'duplicate'):e.packet('sample',plan,root)
    def test_placeholders_axioms_and_kernel_options_fail(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p,d,plan=self.fixture(root)
            for code in ['theorem t : False := by sorry','axiom bad : False','set_option debug.skipKernelTC true','example : True := by native_decide']:
                (p/'Draft.lean').write_text('module\npublic import Base\n'+code+'\n')
                d['files']['Draft.lean']['sha256']=ci.sha(p/'Draft.lean');ci.write_json(p/'intake.json',d)
                with self.assertRaises(ValueError):e.packet('sample',plan,root)
    def test_upstream_and_audit_module_shadowing_fails(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p,d,plan=self.fixture(root)
            for name in sorted(e.OFFICIAL_PREFIXES|{'ExperimentAudit','CheckpointAudit'}):
                (p/(name+'.lean')).write_text('module\n')
                ci.write_json(p/'intake.json',{'order':[name],'files':{
                    name+'.lean':{'sha256':ci.sha(p/(name+'.lean')),'imports':[]}}})
                with self.assertRaisesRegex(ValueError,'shadowing'):e.packet('sample',plan,root)
    def test_nonpreceding_draft_import_fails(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p,d,plan=self.fixture(root)
            (p/'Draft.lean').write_text('module\npublic import Later\n')
            (p/'Later.lean').write_text('module\n')
            d={'order':['Draft','Later'],'files':{n+'.lean':{'sha256':ci.sha(p/(n+'.lean')),'imports':im}
               for n,im in [('Draft',['Later']),('Later',[])]}};ci.write_json(p/'intake.json',d)
            with self.assertRaisesRegex(ValueError,'nonpreceding'):e.packet('sample',plan,root)
    def test_cache_bytes_dependencies_and_scope_fail_closed(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);_,_,plan=self.fixture(root);cache=root/'cache';lib=cache/'lib';lib.mkdir(parents=True)
            entries={}
            for n in ['A','Base']:
                (lib/(n+'.olean')).write_bytes(n.encode())
                entries[n]={'key':plan['module_keys'][n],'files':ci.artifact_hashes(lib,n),
                            'dependency_artifacts':{x:entries[x]['files'] for x in plan['dependencies'][n]}}
            receipt={'schema':ci.SCHEMA,'status':'PASS','base':plan['base'],
                     'scope':'Complete source coverage and recursive axiom audit','modules':entries}
            ci.write_json(cache/'receipt.json',receipt)
            self.assertEqual(set(e.restore_baseline(cache,root/'out',plan,['A','Base'])),{'A','Base'})
            (lib/'Base.olean').write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError,'corrupt'):e.restore_baseline(cache,root/'out2',plan,['A','Base'])
            (lib/'Base.olean').write_bytes(b'Base');receipt['modules']['Base']['dependency_artifacts']={};ci.write_json(cache/'receipt.json',receipt)
            with self.assertRaisesRegex(ValueError,'corrupt'):e.restore_baseline(cache,root/'out3',plan,['A','Base'])
            receipt['scope']='cohort only';ci.write_json(cache/'receipt.json',receipt)
            with self.assertRaisesRegex(ValueError,'full baseline'):e.restore_baseline(cache,root/'out4',plan,['A','Base'])
    def test_audit_private_imports_and_exact_coverage(self):
        text=e.audit_text(['X','Y']);self.assertTrue(text.startswith('module\nimport all X\nimport all Y\n'))
        self.assertIn('let modules : Array Name := #[`X,`Y]',text)
        self.assertIn('unless found == modules.size',text);self.assertIn('collectAxioms name',text)
    def test_workflow_never_saves_draft_cache_or_uploads_oleans(self):
        w=(ci.ROOT/'.github/workflows/progress-experiments.yml').read_text()
        self.assertNotIn('uses: actions/cache/save',w);self.assertIn('path: .cache/progress-ci',w)
        self.assertIn('--seconds 180',w);self.assertNotIn('/lib/',w)
    def test_empty_matrix_skips_checks_without_weakening_admission(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);_,_,plan=self.fixture(root);plan['snapshot']='snapshot'
            output=root/'github-output'
            for names in [[],['sample']]:
                ci.write_json(root/'packets.json',{'active_packets':names})
                output.write_text('')
                with patch.object(e,'EXPERIMENTS',root), patch.object(e.ci,'check_sources'), \
                     patch.object(e.ci,'derive_plan',return_value=plan), \
                     patch.object(e,'packet') as admission, \
                     patch('sys.argv',['check','plan','--github-output',str(output)]):
                    e.main()
                self.assertEqual(admission.call_count,len(names))
                self.assertIn('has_packets='+('true' if names else 'false')+'\n',output.read_text())
                self.assertIn('matrix='+json.dumps({'packet':names},separators=(',',':'))+'\n',output.read_text())
            workflow=(ci.ROOT/'.github/workflows/progress-experiments.yml').read_text()
            self.assertIn("if: needs.plan.outputs.has_packets == 'true'",workflow)

    def test_timeout_is_a_failed_check(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);source=root/'A.lean';source.write_text('module\n')
            with patch.object(e.subprocess,'run',side_effect=e.subprocess.TimeoutExpired('lean',1)):
                row=e.compile_bounded(source,None,root,{},root/'logs',1)
            self.assertEqual(row['exit_code'],124)
            self.assertIn('WALL_CLOCK_LIMIT', (root/'logs/A.log').read_text())

    def revision_fixture(self, root):
        p, d, plan = self.fixture(root)
        previous = root/'previous'; previous.mkdir()
        prior = {'order': ['Draft', 'Stable', 'Retired'], 'files': {}}
        for n in prior['order']:
            source = previous/(n+'.lean')
            source.write_text('module\npublic import Base\n')
            prior['files'][source.name] = {'sha256': ci.sha(source), 'imports': ['Base']}
        ci.write_json(previous/'intake.json', prior)
        for n in ['Stable', 'New']:
            source = p/(n+'.lean'); source.write_text('module\npublic import Base\n')
            d['order'].append(n)
            d['files'][source.name] = {'sha256': ci.sha(source), 'imports': ['Base']}
        d.update(revision_classification_schema=1, revision_of='previous', changed_modules=['Draft'], revised_modules=['Draft'],
                 modified_predecessor_modules=['Draft'], reused_modules=['Stable'],
                 unchanged_predecessor_modules=['Stable'], exact_predecessor_modules=['Stable'],
                 unchanged_producer_modules=1, new_modules=['New'])
        ci.write_json(p/'intake.json', d)
        return p, d, plan, previous, prior

    def test_revision_exact_changed_unchanged_new_and_removed(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); p, d, plan, _, _ = self.revision_fixture(root)
            e.packet('sample', plan, root)
            d['unchanged_producer_modules'] = ['Stable']
            ci.write_json(p/'intake.json', d)
            e.packet('sample', plan, root)
            # Both supported explicit-reference conventions agree.
            d['revision_source'] = 'previous'; ci.write_json(p/'intake.json', d)
            ci.write_json(p/'APPLICATION.json', {'predecessor': 'previous', 'revision_source': 'previous'})
            e.packet('sample', plan, root)

    def test_revision_all_stale_labels_duplicates_and_wrong_counts_fail(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); p, d, plan, _, _ = self.revision_fixture(root)
            for key in ['changed_modules', 'revised_modules', 'modified_predecessor_modules',
                        'reused_modules', 'unchanged_predecessor_modules',
                        'exact_predecessor_modules', 'unchanged_producer_modules', 'new_modules']:
                for value in [[], ['Ghost'], ['Draft', 'Draft'], [1], {}, True, 'Draft']:
                    bad = copy.deepcopy(d); bad[key] = value
                    ci.write_json(p/'intake.json', bad)
                    with self.subTest(key=key, value=value), self.assertRaisesRegex(
                            ValueError, 'Revision classification mismatch: '+key):
                        e.packet('sample', plan, root)
            for count in [-1, 0, 2]:
                bad = copy.deepcopy(d); bad['unchanged_producer_modules'] = count
                ci.write_json(p/'intake.json', bad)
                with self.assertRaisesRegex(ValueError, 'unchanged_producer_modules'):
                    e.packet('sample', plan, root)

    def test_revision_reference_conflicts_unsafe_self_and_missing_fail(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); p, d, plan, _, _ = self.revision_fixture(root)
            for value in ['../previous', '/previous', 'sample', '', [], None]:
                bad = copy.deepcopy(d); bad['revision_of'] = value
                ci.write_json(p/'intake.json', bad)
                with self.assertRaisesRegex(ValueError, 'Invalid revision predecessor'):
                    e.packet('sample', plan, root)
            d['revision_of'] = 'missing'; ci.write_json(p/'intake.json', d)
            with self.assertRaisesRegex(ValueError, 'Missing revision predecessor intake'):
                e.packet('sample', plan, root)
            d['revision_of'] = 'previous'; ci.write_json(p/'intake.json', d)
            ci.write_json(p/'APPLICATION.json', {'predecessor': 'different'})
            with self.assertRaisesRegex(ValueError, 'Conflicting revision predecessors'):
                e.packet('sample', plan, root)

    def test_revision_prior_source_manifest_and_digest_fail(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); p, d, plan, previous, prior = self.revision_fixture(root)
            for order in [['Draft', 'Draft'], ['../Draft'], [], [1]]:
                bad = copy.deepcopy(prior); bad['order'] = order
                ci.write_json(previous/'intake.json', bad)
                with self.assertRaisesRegex(ValueError, 'Invalid revision predecessor source manifest'):
                    e.packet('sample', plan, root)
            ci.write_json(previous/'intake.json', prior)
            (previous/'Draft.lean').write_text('changed predecessor bytes\n')
            with self.assertRaisesRegex(ValueError, 'Revision predecessor source hash mismatch'):
                e.packet('sample', plan, root)
            (previous/'Draft.lean').unlink()
            with self.assertRaisesRegex(ValueError, 'Revision predecessor source hash mismatch'):
                e.packet('sample', plan, root)

    def test_revision_only_bound_root_inheritance_is_used(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); p, d, plan, _, _ = self.revision_fixture(root)
            del d['revision_of']; ci.write_json(p/'intake.json', d)
            ci.write_json(p/'INHERITANCE.json', {'predecessor': 'previous'})
            ci.write_json(p/'APPLICATION.json', {'bindings': {'INHERITANCE.json': ci.sha(p/'INHERITANCE.json')}})
            e.packet('sample', plan, root)
            bad = copy.deepcopy(d); bad['revised_modules'] = ['Stable']
            ci.write_json(p/'intake.json', bad)
            with self.assertRaisesRegex(ValueError, 'revised_modules'):
                e.packet('sample', plan, root)
            # Opted-in packets cannot silently bypass validation without a predecessor.
            ci.write_json(p/'APPLICATION.json', {})
            with self.assertRaisesRegex(ValueError, 'Missing explicit revision predecessor'):
                e.packet('sample', plan, root)
            ci.write_json(p/'APPLICATION.json', {'predecessor': 'different',
                'bindings': {'INHERITANCE.json': ci.sha(p/'INHERITANCE.json')}})
            with self.assertRaisesRegex(ValueError, 'Conflicting revision predecessors'):
                e.packet('sample', plan, root)

    def test_revision_schema_opt_in_preserves_historical_semantics(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); p, d, plan, _, _ = self.revision_fixture(root)
            # Historical packet aliases can describe baseline/new-producer semantics,
            # not the immediate predecessor byte delta. Unversioned means legacy.
            del d['revision_classification_schema']
            d['new_modules'] = ['Draft', 'Stable', 'New']
            d['unchanged_producer_modules'] = 58
            d['revision_of'] = 'historical-predecessor-no-longer-present'
            ci.write_json(p/'intake.json', d)
            e.packet('sample', plan, root)
            for version in [0, 2, True, '1', None, {}]:
                d['revision_classification_schema'] = version
                ci.write_json(p/'intake.json', d)
                with self.assertRaisesRegex(ValueError, 'Unsupported revision classification schema'):
                    e.packet('sample', plan, root)
            d['revision_classification_schema'] = 1
            del d['revision_of']; ci.write_json(p/'intake.json', d)
            with self.assertRaisesRegex(ValueError, 'Missing explicit revision predecessor'):
                e.packet('sample', plan, root)
            d['revision_of'] = 'previous'; ci.write_json(p/'intake.json', d)
            with self.assertRaisesRegex(ValueError, 'Revision classification mismatch'):
                e.packet('sample', plan, root)

if __name__=='__main__':unittest.main()
