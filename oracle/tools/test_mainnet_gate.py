"""Fail-closed W13 controls. Synthetic harness tests are never mainnet evidence."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import unittest.mock
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('mainnet_gate', ROOT / 'tools/mainnet-replay/gate.py')
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)


class GateTests(unittest.TestCase):
    def capture(self, root, count=1):
        m = dict(schema=g.SCHEMA, chain_id='mainnet', nearcore_commit=g.PIN,
                 start_height=10, block_count=count, blocks=[], acquisition_errors=[])
        for h in range(10, 10 + count):
            p = root / f'{h}.json'
            g.write(p, {'block': {'header': {'height': h, 'hash': f'h{h}', 'prev_hash': f'h{h-1}'},
                                 'chunks': [{'shard_id': 0, 'height_included': h, 'chunk_hash': f'c{h}'}]}})
            m['blocks'].append(dict(height=h, artifact=dict(path=p.name, sha256=g.digest(p))))
        g.write(root / 'manifest.json', m)
        return m

    def test_archive_credentials_are_not_in_urls_or_cross_origin_redirects(self):
        for url in ['https://host/block/{height}?apiKey=secret',
                    'https://user:secret@host/block/{height}']:
            with self.assertRaisesRegex(ValueError, 'credential-free'):
                g.fetch_block(1, Path('/unused'), url, 1)
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError):
                g.capture(1, 1, tmp, 'https://host/{height}?apiKey=secret')
            self.assertFalse((Path(tmp) / 'manifest.json').exists())
        req = g.urllib.request.Request('https://a.example/block', headers={'Authorization': 'Bearer secret'})
        redirected = g.ArchiveRedirect().redirect_request(req, None, 302, '', {}, 'https://b.example/block')
        self.assertIsNone(redirected.get_header('Authorization'))
        with self.assertRaises(ValueError):
            g.ArchiveRedirect().redirect_request(req, None, 302, '', {}, 'http://a.example/block')

    def test_rate_limit_retries_with_backoff_then_fails_closed(self):
        err = lambda: g.urllib.error.HTTPError('https://a/1', 429, 'Too Many Requests',
                                               {'Retry-After': '0'}, None)
        class Ok:
            def __enter__(self): return self
            def __exit__(self, *a): return False
            def read(self, n): return b'{}'
        slept = []
        opener = unittest.mock.MagicMock()
        opener.open.side_effect = [err(), err(), Ok()]
        with patch.object(g.urllib.request, 'build_opener', return_value=opener):
            self.assertEqual(g.open_with_retry('req', 1, sleep=slept.append), b'{}')
        self.assertEqual(slept, [2, 4])     # Retry-After: 0 never shortens the backoff
        opener.open.side_effect = [err() for _ in range(3)]
        with patch.object(g.urllib.request, 'build_opener', return_value=opener), \
             self.assertRaises(g.urllib.error.HTTPError):
            g.open_with_retry('req', 1, attempts=3, sleep=lambda d: None)
        opener.open.side_effect = [g.urllib.error.HTTPError('https://a/1', 404, 'nf', {}, None)]
        with patch.object(g.urllib.request, 'build_opener', return_value=opener), \
             self.assertRaises(g.urllib.error.HTTPError):
            g.open_with_retry('req', 1, sleep=lambda d: self.fail('404 must not be retried'))

    def test_archive_sources_and_block_extraction(self):
        g.validate_archive_url('jsonrpc+https://archival-rpc.mainnet.fastnear.com')
        for bad in ['jsonrpc+https://h/{height}', 'jsonrpc+http://h', 'http://h/{height}', 'https://h/x']:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                g.validate_archive_url(bad)
        view = {'header': {'height': 1}, 'chunks': []}
        self.assertIs(g.block_of({'block': view}), view)
        self.assertIs(g.block_of({'jsonrpc': '2.0', 'result': view}), view)
        for doc in [{'error': {'name': 'HANDLER_ERROR'}}, None, {'result': {'chunks': []}}]:
            with self.subTest(doc=doc), self.assertRaises(ValueError):
                g.block_of(doc)

    def test_resume_refetches_only_errors_and_never_overwrites(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            calls = []
            def fetch(height, out_dir, url, timeout, key):
                calls.append(height)
                if height == 11 and len(calls) < 4:
                    raise ValueError('HTTP Error 429')
                p = out_dir / 'blocks' / f'{height}.json'
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text('{}')
                return {}, {'path': f'blocks/{height}.json', 'sha256': g.digest(p)}
            with patch.object(g, 'fetch_block', side_effect=fetch):
                m = g.capture(10, 3, out, 'https://h/{height}')
                self.assertEqual([e['height'] for e in m['acquisition_errors']], [11])
                with self.assertRaisesRegex(ValueError, 'already exists'):
                    g.capture(10, 3, out, 'https://h/{height}')
                with self.assertRaisesRegex(ValueError, 'same window'):
                    g.capture(10, 4, out, 'https://h/{height}', resume=True)
                m = g.capture(10, 3, out, 'https://h/{height}', resume=True)
            self.assertEqual(calls, [10, 11, 12, 11])
            self.assertEqual([b['height'] for b in m['blocks']], [10, 11, 12])
            self.assertEqual(m['acquisition_errors'], [])

    def test_zero_comparisons_is_not_zero_mismatch(self):
        r = g.summarize([{'status': 'missing_witness'}], 1, 1000, 1000, [])
        self.assertIsNone(r['mismatch_percent'])
        self.assertEqual(r['status'], 'fail')
        self.assertEqual(r['replay_coverage_percent'], 0)

    def test_denominator_and_partial_coverage(self):
        rows = [{'status': s} for s in ['match', 'mismatch', 'unsupported', 'error', 'missing_witness']]
        r = g.summarize(rows, 5, 1000, 1000, [])
        self.assertEqual(r['mismatch_percent'], 50)
        self.assertEqual(r['replay_coverage_percent'], 40)
        self.assertEqual(r['verified_match_percent'], 20)
        self.assertEqual(r['status'], 'fail')

    def test_only_complete_zero_mismatch_passes(self):
        rows = [{'status': 'match'}] * 3
        self.assertEqual(g.summarize(rows, 3, 1000, 1000, [])['status'], 'pass')
        for expected, blocks, errors in [(4, 1000, []), (3, 999, []), (3, 1000, ['capture error'])]:
            self.assertEqual(g.summarize(rows, expected, blocks, 1000, errors)['status'], 'fail')
        self.assertEqual(g.summarize([], 0, 1000, 1000, [])['status'], 'fail')

    def test_missing_manifest_overwrites_old_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            g.write(root / 'out/report.json', {'status': 'pass'})
            r = g.replay(root, sys.executable, 'curveHosts', None, root / 'out')
            self.assertEqual(r['status'], 'fail')
            self.assertEqual(json.loads((root / 'out/report.json').read_text())['status'], 'fail')

    def test_missing_cases_and_small_window_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.capture(root, 2)
            r = g.replay(root, sys.executable, 'curveHosts', None, root / 'out')
            self.assertEqual(r['expected_chunks'], 2)
            self.assertEqual(r['counts'], {'missing_witness': 2})
            self.assertEqual(r['status'], 'fail')
            with self.assertRaises(ValueError):
                g.replay(root, sys.executable, 'curveHosts', None, root / 'out', minimum_blocks=2)

    def test_inventory_rejects_tamper_duplicates_foreign_and_escape(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for kind in ['tamper', 'duplicate', 'foreign', 'escape']:
                m = self.capture(root)
                if kind == 'tamper': (root / '10.json').write_text('{}')
                if kind == 'duplicate': m['blocks'] *= 2
                if kind == 'foreign': m['blocks'][0]['height'] = 99
                if kind == 'escape': m['blocks'][0]['artifact']['path'] = '../outside.json'
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    g.inventory(m, root)

    def test_capture_shards_are_derived_not_supplied_by_case_list(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            m = self.capture(root)
            p = root / '10.json'
            b = json.loads(p.read_text())
            b['block']['chunks'].append(dict(shard_id=1, height_included=9, chunk_hash='old'))
            g.write(p, b)
            m['blocks'][0]['artifact']['sha256'] = g.digest(p)
            _, rows, _ = g.inventory(m, root)
            self.assertEqual(len(rows), 2)
            self.assertEqual(sum(r['new_chunk'] for r in rows), 1)

    def test_native_receipt_binds_inputs_and_chain(self):
        entry = dict(block_hash='block', chunk_hash='chunk')
        hashes = {'claim.bin': 'c', 'witness.bin': 'w'}
        fin = dict(final=True, canonical=True, included_block_hash='block')
        cold = dict(policy='cold', entries_before=0)
        row = dict(chain_id='mainnet', nearcore_commit=g.PIN, block_hash='block', chunk_hash='chunk',
                   claim_sha256='c', witness_sha256='w', facts_verified=True, verdict='accept',
                   finality=fin, cache=cold)
        for change in [{}, {'witness_sha256': 'wrong'}, {'nearcore_commit': 'wrong'}, {'facts_verified': 1},
                       {'verdict': 'oops'}, {'finality': None}, {'finality': fin | {'final': False}},
                       {'finality': fin | {'canonical': False}},
                       {'finality': fin | {'included_block_hash': 'fork'}},
                       {'cache': None}, {'cache': cold | {'policy': 'warm'}},
                       {'cache': cold | {'entries_before': 3}}]:
            with patch.object(g.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, json.dumps(row | change))):
                if change:
                    with self.assertRaises(ValueError):g.native_check(['native'], Path('case'), entry, hashes, 1)
                else:self.assertEqual(g.native_check(['native'], Path('case'), entry, hashes, 1)['verdict'], 'accept')

    def test_native_crash_and_timeout_are_not_mismatches(self):
        for error in [subprocess.CalledProcessError(1, []), subprocess.TimeoutExpired([], 1)]:
            with patch.object(g.subprocess, 'run', side_effect=error), self.assertRaises(type(error)):
                g.native_check(['native'], Path('case'), {}, {}, 1)

    def test_claim_chunk_and_segment_binding(self):
        source = ROOT / 'oracle/wasm-d3/tests/d3_smoke/cases/d3c7-d3-00-h10004-s1'
        claim = g.wire.decode_claim((source / 'claim.bin').read_bytes())
        claim['chain_id'] = b'mainnet'  # Synthetic unit test only, never a mainnet fixture.
        inner = g.wire.decode_inner_bytes(claim['chunk_inner'])
        blocks = {i: {'header': {'hash': g.b58(g.wire.block_hash(b)),
                                'epoch_id': g.b58(claim['epoch_id'])}}
                  for i, b in enumerate(claim['blocks'])}
        entry = dict(height=0, shard_id=inner.shard_id, chunk_hash=g.b58(inner.chunk_hash))
        with tempfile.TemporaryDirectory() as tmp:
            case = Path(tmp);(case / 'claim.bin').write_bytes(b'placeholder')
            g.write(case / 'context-blocks.json', [])
            with patch.object(g.wire, 'decode_claim', return_value=claim):
                self.assertEqual(g.anchor_case(case, entry, blocks), {})
                with self.assertRaisesRegex(ValueError, 'commitment'):
                    g.anchor_case(case, entry | {'chunk_hash': 'substituted'}, blocks)
                blocks[0]['header']['hash'] = 'substituted'
                with self.assertRaisesRegex(ValueError, 'segment'):
                    g.anchor_case(case, entry, blocks)

    def test_generated_claim_cannot_be_relabelled_mainnet(self):
        source = ROOT / 'oracle/wasm-d3/tests/d3_smoke/cases/d3c7-d3-00-h10004-s1'
        with self.assertRaisesRegex(ValueError, 'not mainnet'):
            g.anchor_case(source, {}, {})

    def test_rebased_historical_fixture_cannot_pass(self):
        source = ROOT / 'oracle/fixtures/historical/cases/mainnet-s12-h218303553'
        with self.assertRaises(Exception):
            g.anchor_case(source, {}, {})

    def test_replay_partitions_results_without_hiding_missing_cases(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp);self.capture(root, 5)
            for h in range(10, 14):
                case = root / f'cases/h{h}-s0';case.mkdir(parents=True)
                (case / 'claim.bin').write_bytes(b'claim')
                (case / 'witness.bin').write_bytes(b'witness')
                g.write(case / 'context-blocks.json', [])
            def lean(binary, tier, case, blind_dir, timeout):
                h = int(case.name.split('-')[0][1:])
                if h == 13:raise subprocess.TimeoutExpired([], 1)
                return {10: 'match', 11: 'mismatch', 12: 'unsupported'}[h], {}
            with patch.object(g, 'anchor_case', return_value={}), \
                 patch.object(g, 'native_check', return_value={'verdict': 'accept'}), \
                 patch.object(g, 'lean_blind', side_effect=lean):
                r = g.replay(root, sys.executable, 'curveHosts', [sys.executable], root / 'out')
            self.assertEqual(r['counts'], {'match': 1, 'mismatch': 1, 'unsupported': 1, 'error': 1, 'missing_witness': 1})
            self.assertEqual(r['mismatch_percent'], 50)
            self.assertEqual(r['replay_coverage_percent'], 40)
            self.assertEqual(r['status'], 'fail')

    def test_native_rejection_cannot_be_counted_as_lean_match(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp);self.capture(root)
            case = root / 'cases/h10-s0';case.mkdir(parents=True)
            for f in ('claim.bin', 'witness.bin'):(case / f).write_bytes(b'x')
            g.write(case / 'context-blocks.json', [])
            with patch.object(g, 'anchor_case', return_value={}), \
                 patch.object(g, 'native_check', return_value={'verdict': 'reject'}), \
                 patch.object(g, 'lean_blind') as lean:
                r = g.replay(root, sys.executable, 'curveHosts', [sys.executable], root / 'out')
                lean.assert_not_called()
            self.assertEqual(r['counts'], {'native_reject': 1})
            self.assertIsNone(r['mismatch_percent'])

    def test_changed_artifacts_invalidate_run(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp);self.capture(root)
            case = root / 'cases/h10-s0';case.mkdir(parents=True)
            for f in ('claim.bin', 'witness.bin'):(case / f).write_bytes(b'x')
            g.write(case / 'context-blocks.json', [])
            def mutate(*args):
                (case / 'witness.bin').write_bytes(b'changed')
                return 'match', {}
            with patch.object(g, 'anchor_case', return_value={}), \
                 patch.object(g, 'native_check', return_value={'verdict': 'accept'}), \
                 patch.object(g, 'lean_blind', side_effect=mutate):
                r = g.replay(root, sys.executable, 'curveHosts', [sys.executable], root / 'out')
            self.assertTrue(any('artifact changed' in e for e in r['errors']))
            self.assertEqual(r['status'], 'fail')

    def test_blind_output_mismatch_and_leak_count_as_mismatches(self):
        rows = [{'status': s, 'shard_id': i % 2} for i, s in
                enumerate(['match', 'output_mismatch', 'blind_leak', 'mismatch', 'missing_witness'])]
        r = g.summarize(rows, 5, 1000, 1000, [])
        self.assertEqual(r['compared_chunks'], 4)
        self.assertEqual(r['mismatch_percent'], 75)
        self.assertEqual(r['per_shard'], {'0': {'match': 1, 'blind_leak': 1, 'missing_witness': 1},
                                          '1': {'output_mismatch': 1, 'mismatch': 1}})
        self.assertEqual(r['status'], 'fail')

    def test_blind_status_classification(self):
        lean = lambda verdict, outputs=None: {'verdict': verdict, 'outputs': outputs}
        expected = {k: 'x' for k in g.blind_inputs.COMPARED}
        cases = [
            (lean('accept', expected), lean('reject'), 'match'),
            (lean('accept', expected | {'stateRoot': 'y'}), lean('reject'), 'output_mismatch'),
            (lean('accept', expected), lean('accept'), 'blind_leak'),
            (lean('reject'), lean('reject'), 'mismatch'),
            (lean('out_of_domain'), lean('reject'), 'unsupported'),
        ]
        for blind, control, status in cases:
            with self.subTest(status=status), \
                 patch.object(g.blind_inputs, 'blind_case', return_value=(expected, {'implicit_transitions': 0})), \
                 patch.object(g, 'lean_run', side_effect=[blind, control]):
                self.assertEqual(g.lean_blind('bin', 'allFeatures', Path('c'), Path('b'), 1)[0], status)

    def test_pack_witness_preserves_raw_and_verifies_code(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            raw, code, out = root / 'raw', root / 'code', root / 'witness'
            raw.write_bytes(b'raw-nearcore-witness')
            code.write_bytes(b'wasm')
            g.pack_witness(raw, [g.digest(code) + '=' + str(code)], out)
            r = g.wire.R(out.read_bytes())
            self.assertEqual(r.bytes(), g.wire.FORMAT_WITNESS)
            self.assertEqual(r.bytes(), raw.read_bytes())
            self.assertEqual(r.vec(r.bytes), [code.read_bytes()])
            r.end()
            with self.assertRaises(ValueError):g.pack_witness(raw, [], out)
            with self.assertRaisesRegex(ValueError, 'SHA256'):
                g.pack_witness(raw, ['0' * 64 + '=' + str(code)], root / 'bad')

    def test_block_chain_discontinuity_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp);m = self.capture(root, 2)
            p = root / '11.json';b = json.loads(p.read_text())
            b['block']['header']['prev_hash'] = 'fork'
            g.write(p, b);m['blocks'][1]['artifact']['sha256'] = g.digest(p)
            with self.assertRaisesRegex(ValueError, 'discontinuity'):g.inventory(m, root)


if __name__ == '__main__':
    unittest.main()
