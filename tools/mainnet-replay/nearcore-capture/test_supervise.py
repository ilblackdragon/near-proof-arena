import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('supervise', Path(__file__).with_name('supervise.py'))
supervise = importlib.util.module_from_spec(spec)
spec.loader.exec_module(supervise)


class ProtocolGuardTests(unittest.TestCase):
    now = 1792884413

    def node(self, version, timestamp='2026-10-24T23:26:00Z', syncing=False):
        return dict(chain_id='mainnet', protocol_version=version,
                    sync_info=dict(latest_block_time=timestamp, syncing=syncing))

    def test_genesis_after_reset_is_allowed_even_when_not_syncing(self):
        self.assertIsNone(supervise.protocol_stop_reason(
            self.node(29, '2020-07-21T16:55:51.591948000Z'), self.now))

    def test_current_pinned_head_is_allowed(self):
        self.assertIsNone(supervise.protocol_stop_reason(self.node(86), self.now))

    def test_recent_unexpected_protocol_is_rejected(self):
        self.assertIsNotNone(supervise.protocol_stop_reason(self.node(85), self.now))

    def test_upgrade_is_rejected_even_during_sync(self):
        self.assertIsNotNone(supervise.protocol_stop_reason(self.node(87, syncing=True), self.now))

    def test_missing_status_does_not_become_mismatch(self):
        self.assertIsNone(supervise.protocol_stop_reason({}, self.now))

    def test_wrong_network_is_rejected(self):
        self.assertIsNotNone(supervise.protocol_stop_reason({'chain_id': 'testnet'}, self.now))


if __name__ == '__main__':
    unittest.main()
