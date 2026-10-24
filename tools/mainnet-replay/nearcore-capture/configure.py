#!/usr/bin/env python3
"""Configure an already initialized isolated PV86 mainnet capture node."""
import argparse
import hashlib
import ipaddress
import json
from pathlib import Path
import urllib.request

PIN = '44f7ae6cd7ef08bab604e20a473bf77e35d4c993'


def rpc(endpoint, method, params):
    req = urllib.request.Request(endpoint, json.dumps(dict(jsonrpc='2.0', id='w13', method=method, params=params)).encode(),
                                 headers={'Content-Type': 'application/json'})
    with urllib.request.urlopen(req, timeout=30) as response:
        data = json.load(response)
    if 'error' in data:
        raise ValueError(data['error'])
    return data['result']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--home', type=Path, required=True)
    p.add_argument('--rpc', default='https://rpc.mainnet.fastnear.com')
    p.add_argument('--shard', type=int, default=13)
    a = p.parse_args()
    status = rpc(a.rpc, 'status', [])
    if status['chain_id'] != 'mainnet' or status['protocol_version'] != 86:
        raise ValueError('live network is not the pinned mainnet PV86 target')
    protocol = rpc(a.rpc, 'EXPERIMENTAL_protocol_config', {'finality': 'final'})
    layout = next(iter(protocol['shard_layout'].values()))
    if a.shard not in layout['shard_ids']:
        raise ValueError('requested shard is absent from the live shard layout')
    peers = rpc(a.rpc, 'network_info', {})['active_peers']
    boots = []
    for peer in peers:
        addr = peer.get('addr')
        if addr:
            try:
                host = addr.rsplit(':', 1)[0].strip('[]')
                if ipaddress.ip_address(host).is_global:
                    boots.append(peer['id'] + '@' + addr)
            except ValueError:
                continue
    if len(boots) < 3:
        raise ValueError('insufficient public boot peers')
    path = a.home / 'config.json'
    config = json.loads(path.read_text())
    if (a.home / 'data').exists():
        raise ValueError('refusing configuration changes to an existing node database')
    config['tracked_shards_config'] = {'Schedule': [[a.shard]]}
    for key in ('tracked_shards', 'tracked_accounts', 'tracked_shard_schedule'):
        config.pop(key, None)
    config['save_latest_witnesses'] = True
    config['save_invalid_witnesses'] = True
    config['archive'] = False
    config['gc_num_epochs_to_keep'] = 3
    config['rpc']['addr'] = '127.0.0.1:3038'
    config['rpc']['prometheus_addr'] = '127.0.0.1:3039'
    config['network']['addr'] = '0.0.0.0:24578'
    config['network']['boot_nodes'] = ','.join(boots[:30])
    config['network']['max_num_peers'] = 30
    config['network']['ideal_connections_lo'] = 10
    config['network']['ideal_connections_hi'] = 20
    config['telemetry'] = {'endpoints': []}
    path.write_text(json.dumps(config, indent=2) + '\n')
    evidence = dict(nearcore_pin=PIN, mainnet_status=status, selected_shards=[a.shard],
                    scope='single-shard acquisition pilot; not W13 all-shard completion',
                    config_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    (a.home / 'setup-evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps({'chain_id': status['chain_id'], 'protocol_version': status['protocol_version'],
                      'boot_peers': len(boots[:30]), 'shard': a.shard, 'rpc': config['rpc']['addr']}))


if __name__ == '__main__':
    main()
