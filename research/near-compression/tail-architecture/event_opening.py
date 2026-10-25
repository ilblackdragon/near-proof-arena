#!/usr/bin/env python3
"""Algebra prototype, NOT a PCS: open a virtual trace from change events.

No array indexed by virtual trace height is constructed by event_opening.
Challenges and arithmetic use a small prime solely for identity testing.
"""
import json
import random

P = 2013265921


def prefix_weight(bound, point):
    """Sum eq(point,t) for 0 <= t < bound; point is little-endian.

    Digit DP over the bound, valid for arbitrary field challenges, not just
    probability weights. O(log height) field operations, O(1) extra space.
    """
    height = 1 << len(point)
    assert 0 <= bound <= height
    if bound == height:
        return 1
    total, equal = 0, 1
    for bit in reversed(range(len(point))):
        r = point[bit]
        if (bound >> bit) & 1:
            total = (total + equal * (1-r)) % P
            equal = equal * r % P
        else:
            equal = equal * (1-r) % P
    return total


def event_opening(events, point):
    """Events (position,delta) define f[t] = sum_{position<=t} delta.

    A real protocol must authenticate events, their domain and completeness.
    The algebra alone permits arbitrary prover-chosen events.
    """
    return sum(delta * (1-prefix_weight(pos, point))
               for pos, delta in events) % P


def dense_opening(values, point):
    values = list(values)
    for r in point:
        values = [(a+r*(b-a)) % P for a, b in zip(values[::2], values[1::2])]
    assert len(values) == 1
    return values[0]


def check():
    rng = random.Random(20261024)
    checks = 0
    for log_height in range(1, 10):
        height = 1 << log_height
        points = [[rng.randrange(P) for _ in range(log_height)],
                  [0]*log_height, [1]*log_height]
        for point in points:
            weights = [1]
            for r in point:
                weights = [v*(1-r) % P for v in weights] + [v*r % P for v in weights]
            cumulative = 0
            for bound in range(height+1):
                assert prefix_weight(bound, point) == cumulative
                if bound < height:
                    cumulative = (cumulative+weights[bound]) % P
                checks += 1
            events = [(0, rng.randrange(P))]
            events += [(pos, rng.randrange(P)) for pos in range(1, height) if rng.random() < .1]
            values, current, deltas = [], 0, dict(events)
            for t in range(height):
                current = (current+deltas.get(t, 0)) % P
                values.append(current)
            assert event_opening(events, point) == dense_opening(values, point)
            checks += 1
    # Mutation illustrates the authentication obligation: omitted events change
    # the answer, yet this evaluator has no commitment with which to reject them.
    assert event_opening([(0, 3), (4, 7)], [2, 3, 5]) != event_opening([(0, 3)], [2, 3, 5])
    return {'status': 'ALGEBRA_IDENTITIES_ONLY', 'checks': checks,
            'virtual_height_allocation': False, 'authenticated': False,
            'security_established': False}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
