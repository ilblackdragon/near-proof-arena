import sys
from pathlib import Path

# Make `arena_bench` importable when pytest runs from the repo root or benchmarks/.
sys.path.insert(0, str(Path(__file__).resolve().parent))
