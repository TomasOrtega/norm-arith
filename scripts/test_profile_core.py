"""Check profile parsing and failure reporting without launching Lean."""

import json
import unittest

from profile_core import profile_metrics, read_replay, replace_proof, summarize


class CoreProfileTests(unittest.TestCase):
    def test_reads_replay_from_json_message(self):
        payload = json.dumps([1, 0, [[8, 1]]])
        tactic = 'norm_arith_replay ' + json.dumps(payload)
        output = json.dumps({'data': 'Try this:\n  ' + tactic})
        replay, metadata = read_replay(output)
        self.assertEqual(replay, tactic)
        self.assertEqual(metadata['graph_nodes'], 1)
        self.assertEqual(metadata['certificate_bytes'], len(payload.encode()))

    def test_rejects_missing_or_unknown_replay(self):
        with self.assertRaises(ValueError):
            read_replay('no suggestion')
        with self.assertRaises(ValueError):
            read_replay('norm_arith_replay "[2,0,[]]"')

    def test_lean_suggestion_can_omit_space_before_string(self):
        replay, _ = read_replay('Try this:\n  [apply] norm_arith_replay"[1,0,[[8,1]]]"')
        self.assertEqual(replay, 'norm_arith_replay "[1,0,[[8,1]]]"')

    def test_replay_is_not_inside_marker_comment(self):
        source = ('-- BENCHMARK-STATEMENT\nexample : True := by\n'
                  '  -- BENCHMARK-PROOF\n  trivial\n  -- BENCHMARK-END\n')
        self.assertIn('-- BENCHMARK-PROOF\n  exact True.intro\n',
                      replace_proof(source, 'exact True.intro'))

    def test_phase_times_and_memory_units(self):
        output = json.dumps({'data': '[norm_arith.profile] search_ns=12 reconstruction_ns=34 proof_nodes=56'})
        result = profile_metrics(output, ' 4096 maximum resident set size', 'Darwin')
        self.assertEqual(result['peak_rss_bytes'], 4096)
        self.assertEqual(result['search_ns'], 12)
        self.assertEqual(result['reconstruction_ns'], 34)
        self.assertEqual(profile_metrics('', 'NORM_ARITH_MAX_RSS_KB=4', 'Linux')['peak_rss_bytes'], 4096)

    def test_failure_prevents_a_successful_summary(self):
        samples = [{'phase': 'measure', 'case': 'one', 'variant': variant,
                    'success': variant != 'replay', 'seconds': 1.0}
                   for variant in ('reference', 'lp', 'replay')]
        result = summarize(samples, ['one'])
        self.assertFalse(result['all_succeeded'])
        self.assertIsNone(result['cases'][0]['variants']['replay']['median_seconds'])
        self.assertIsNone(result['cases'][0]['variants']['lp']['median_search_ns'])

    def test_missing_variant_is_a_failure(self):
        self.assertFalse(summarize([], ['one'])['all_succeeded'])


if __name__ == '__main__':
    unittest.main()
