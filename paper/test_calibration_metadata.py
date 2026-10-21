"""Synthetic blinded calibration records; no measured paper evidence."""

import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import generate


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixture(root, block_pairs):
    root.mkdir(parents=True, exist_ok=True)
    specifications = {}
    for key in ['diagnostics_source', 'calibration_review_source']:
        path = root / (key + '.py')
        path.write_text('# Synthetic source fingerprint.\n')
        specifications[key] = {'path': str(path), 'sha256': digest(path)}
    acf = {str(i): (None if i == 3 else 0.1 / i) for i in range(1, 5)}
    correlations = {key: dict(acf) for key in ['original_seconds', 'replacement_seconds', 'log_paired_ratio']}
    blocks = {str(b): {'pilot_blocks': 24 // b, 'confirmatory_pairs': 10 * b, 'confirmatory_blocks': 10,
              'lag_autocorrelations': {key: dict(acf) for key in [
                  'original_mean_seconds_per_pair', 'replacement_mean_seconds_per_pair', 'log_ratio_of_block_totals']}}
              for b in [4, 8]}
    review = {'schema_version': 1, 'scope': 'Speed-level-blinded calibration; synthetic unit fixture.',
              'measured_pairs': 24, 'affected_files': 1, 'pair_series_autocorrelations': correlations,
              'AB_minus_BA': {'original_relative_duration_difference': 0.01,
                  'replacement_relative_duration_difference': 0.02, 'mean_log_paired_ratio_difference': -0.01},
              'half_run_drift': {'original_relative_mean_change': 0.01,
                  'replacement_relative_mean_change': 0.02, 'change_in_mean_log_paired_ratio': -0.01},
              'candidate_blocks': blocks, 'limits': 'Synthetic values; independence is not established.',
              'input_sha256': {'pilot_report': 'a' * 64, 'pilot_measurements': 'b' * 64,
                  'diagnostic_source': specifications['diagnostics_source']['sha256'],
                  'review_source': specifications['calibration_review_source']['sha256']}}
    review_path = root / 'review.json'
    review_path.write_text(json.dumps(review))
    specifications['calibration_review'] = {'path': str(review_path), 'sha256': digest(review_path)}
    decision = {'schema_version': 1, 'date': '2026-10-21', 'block_pairs': block_pairs,
                'rationale': 'Synthetic dependence rationale, unrelated to speed.',
                'pilot_report': {'path': 'absent-pilot-report.json', 'sha256': 'a' * 64},
                'pilot_measurements': {'path': 'absent-pilot.jsonl', 'sha256': 'b' * 64},
                'speed_level_blinded': True, 'review_inputs': {str(review_path): digest(review_path)},
                'review_source_sha256': specifications['calibration_review_source']['sha256'],
                'predeclared_confirmatory_pairs': 10 * block_pairs}
    decision_path = root / 'calibration.json'
    decision_path.write_text(json.dumps(decision))
    specifications['calibration_decision'] = {'path': str(decision_path), 'sha256': digest(decision_path)}
    plan = {'measured_pairs': 10 * block_pairs, 'affected_files': ['Mathlib/Synthetic.lean'],
            'calibration': {**decision, 'path': str(decision_path), 'sha256': digest(decision_path)}}
    plan_path = root / 'plan.json'
    plan_path.write_text(json.dumps(plan))
    config = {'study_mode': 'composed_expansion', 'paper_metadata': specifications,
              'confirmatory_analysis_plan': str(plan_path)}
    evidence = {'timing': {'block_count': 10, 'block_pairs': block_pairs}}
    return config, evidence, review, decision, plan


def add_export_metadata(f, block_pairs):
    import evidence
    config, _, review, decision, _ = fixture(f.root / 'synthetic-blinded-review', block_pairs)
    calibration = f.plan['calibration']
    pilot_path = Path(calibration['pilot_report']['path'])
    pilot = json.loads(pilot_path.read_bytes())
    pilot['provenance']['repetitions'] = 24
    pilot['measurements'] = [r for r in pilot['measurements'] if r['phase'] != 'measured' or r['pair'] < 24]
    pilot['summary'] = evidence.BENCHMARK.summarize(pilot['measurements'], [f.path], 24)
    pilot_path.write_text(json.dumps(pilot))
    raw = Path(calibration['pilot_measurements']['path'])
    raw.write_text(''.join(json.dumps(r) + '\n' for r in pilot['measurements']))
    review['input_sha256'].update(pilot_report=digest(pilot_path), pilot_measurements=digest(raw))
    specs = config['paper_metadata']
    review_path = Path(specs['calibration_review']['path'])
    review_path.write_text(json.dumps(review))
    specs['calibration_review']['sha256'] = digest(review_path)
    decision['review_inputs'] = {str(review_path): digest(review_path)}
    for key, path in [('pilot_report', pilot_path), ('pilot_measurements', raw)]:
        decision[key] = {'path': str(path), 'sha256': digest(path)}
    calibration_path = Path(calibration['path'])
    calibration_path.write_text(json.dumps(decision))
    specs['calibration_decision'] = {'path': str(calibration_path), 'sha256': digest(calibration_path)}
    f.config['paper_metadata'] = specs
    f.plan['calibration'] = evidence.BENCHMARK.validate_calibration(
        calibration_path, f.timing_report['provenance'], [f.path])
    f.save_timing()


class BlindedCalibrationTests(unittest.TestCase):
    def generate(self, config, evidence, output, inputs=None):
        with patch.object(generate, 'GENERATED', output):
            return generate.metadata_data(config, evidence, inputs)

    def test_both_predeclared_designs_need_no_unblinded_diagnostics(self):
        for b in [4, 8]:
            with self.subTest(block_pairs=b), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                config, evidence, *_ = fixture(root / 'inputs', b)
                output = root / 'generated'; output.mkdir()
                self.generate(config, evidence, output)
                text = (output / 'calibration-status.tex').read_text()
                self.assertIn(f'selected {b} pairs', text)
                self.assertIn('24-pair pilot', text)
                self.assertIn('Undefined', (output / 'calibration-table.tex').read_text())
                self.assertNotIn('pilot_diagnostics', config['paper_metadata'])

    def test_copied_metadata_works_after_live_inputs_are_removed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config, evidence, *_ = fixture(root / 'live', 8)
            copied = root / 'copied'; copied.mkdir()
            inputs = {}
            for key, spec in config['paper_metadata'].items():
                target = copied / Path(spec['path']).name
                shutil.copyfile(spec['path'], target); inputs['metadata_' + key] = target
            shutil.copyfile(config['confirmatory_analysis_plan'], copied / 'plan.json')
            inputs['final_analysis_plan'] = copied / 'plan.json'
            shutil.rmtree(root / 'live')
            output = root / 'generated'; output.mkdir()
            self.generate(config, evidence, output, inputs)
            self.assertTrue((output / 'calibration-table.tex').is_file())

    def test_changed_blinding_lineage_or_design_is_rejected(self):
        mutations = [lambda r,d,p: r['input_sha256'].__setitem__('pilot_report', 'f' * 64),
                     lambda r,d,p: d.__setitem__('speed_level_blinded', False),
                     lambda r,d,p: d.__setitem__('review_source_sha256', 'f' * 64),
                     lambda r,d,p: d.__setitem__('predeclared_confirmatory_pairs', 80),
                     lambda r,d,p: r['candidate_blocks']['4'].__setitem__('confirmatory_pairs', 80),
                     lambda r,d,p: r.__setitem__('mean_speed_ratio', 2.0)]
        for mutate in mutations:
            with self.subTest(mutation=mutate), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                config, evidence, review, decision, plan = fixture(root / 'inputs', 4)
                mutate(review, decision, plan)
                review_path = Path(config['paper_metadata']['calibration_review']['path'])
                review_path.write_text(json.dumps(review))
                config['paper_metadata']['calibration_review']['sha256'] = digest(review_path)
                decision['review_inputs'][str(review_path)] = digest(review_path)
                decision_path = Path(config['paper_metadata']['calibration_decision']['path'])
                decision_path.write_text(json.dumps(decision))
                config['paper_metadata']['calibration_decision']['sha256'] = digest(decision_path)
                plan['calibration'].update(sha256=digest(decision_path))
                Path(config['confirmatory_analysis_plan']).write_text(json.dumps(plan))
                output = root / 'generated'; output.mkdir()
                with self.assertRaises(ValueError):
                    self.generate(config, evidence, output)


if __name__ == '__main__':
    unittest.main()
