"""Host profile collector (no sudo). docs/BENCHMARK_SPEC.md §4.

Output document (`arena-host-profile-v1`):

  {
    "schema": "arena-host-profile-v1",
    "governed": false,                # true only for judge benchmark hosts
    "hardware_profile": {             # exactly arena_types::HardwareProfile
      "id", "cpu_model", "vcpus", "ram_bytes", "gpu"
    },
    "details": {...},                 # everything else, informational
    "warnings": [...],                # deviations from governed-host policy
    "collected_at": "RFC3339 UTC"
  }

Only `hardware_profile` is compared against a challenge's `hardware_profile`;
`details` feeds the report and the governed-host checklist.
"""

from __future__ import annotations

import datetime as _dt
import glob
import os
import platform
import re
import shutil
import subprocess
from pathlib import Path
from typing import Callable, Optional

SCHEMA = "arena-host-profile-v1"


def _read(path: str) -> Optional[str]:
    try:
        return Path(path).read_text(errors="replace").strip()
    except OSError:
        return None


def parse_cpulist(s: str) -> list[int]:
    """'0-3,8,10-11' -> [0,1,2,3,8,10,11]. Empty string -> []."""
    out: list[int] = []
    s = s.strip()
    if not s or s == "(null)":  # sysfs prints "(null)" when e.g. nohz_full is unset
        return out
    for part in s.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, b = part.split("-", 1)
            out.extend(range(int(a), int(b) + 1))
        else:
            out.append(int(part))
    return out


def parse_cpuinfo(text: str) -> dict:
    """First processor block fields + set of distinct microcode revisions."""
    blocks = [b for b in text.split("\n\n") if b.strip()]
    first: dict[str, str] = {}
    microcodes: set[str] = set()
    for i, b in enumerate(blocks):
        kv = {}
        for line in b.splitlines():
            if ":" in line:
                k, v = line.split(":", 1)
                kv[k.strip()] = v.strip()
        if "microcode" in kv:
            microcodes.add(kv["microcode"])
        if i == 0:
            first = kv
    flags = set(first.get("flags", first.get("Features", "")).split())
    return {
        "model_name": first.get("model name") or first.get("Hardware") or first.get("CPU part") or "unknown",
        "vendor_id": first.get("vendor_id"),
        "cpu_family": first.get("cpu family"),
        "model": first.get("model"),
        "stepping": first.get("stepping"),
        "microcode": sorted(microcodes),
        "hypervisor": "hypervisor" in flags,
        "isa_flags": sorted(flags & {"avx2", "avx512f", "avx512ifma", "bmi2", "adx", "sha_ni", "vaes", "vpclmulqdq", "aes", "sve", "sve2"}),
    }


def parse_meminfo(text: str) -> dict:
    out = {}
    for line in text.splitlines():
        m = re.match(r"^(\w+):\s+(\d+)\s*(kB)?", line)
        if m:
            v = int(m.group(2))
            out[m.group(1)] = v * 1024 if m.group(3) else v
    return out


def parse_cmdline_isolation(cmdline: str) -> dict:
    keys = ("isolcpus", "nohz_full", "rcu_nocbs", "irqaffinity", "intel_pstate", "mitigations", "transparent_hugepage")
    out = {}
    for tok in cmdline.split():
        k, _, v = tok.partition("=")
        if k in keys:
            out[k] = v
    return out


def _governors(root: str) -> dict:
    vals: dict[str, int] = {}
    for p in sorted(glob.glob(f"{root}/sys/devices/system/cpu/cpu[0-9]*/cpufreq/scaling_governor")):
        g = _read(p)
        if g:
            vals[g] = vals.get(g, 0) + 1
    return vals


def _turbo(root: str) -> dict:
    c0 = f"{root}/sys/devices/system/cpu/cpu0/cpufreq"
    no_turbo = _read(f"{root}/sys/devices/system/cpu/intel_pstate/no_turbo")
    boost = _read(f"{root}/sys/devices/system/cpu/cpufreq/boost") or _read(f"{c0}/boost")
    enabled: Optional[bool] = None  # None = could not determine without privileges
    if no_turbo is not None:
        enabled = no_turbo == "0"
    elif boost is not None:
        enabled = boost == "1"
    return {
        "enabled": enabled,
        "intel_pstate_no_turbo": no_turbo,
        "cpufreq_boost": boost,
        "scaling_driver": _read(f"{c0}/scaling_driver"),
        "amd_pstate_status": _read(f"{root}/sys/devices/system/cpu/amd_pstate/status"),
        "energy_performance_preference": _read(f"{c0}/energy_performance_preference"),
        "cpuinfo_max_khz": _read(f"{c0}/cpuinfo_max_freq"),
        "scaling_max_khz": _read(f"{c0}/scaling_max_freq"),
    }


def _numa(root: str) -> list[dict]:
    nodes = []
    for d in sorted(glob.glob(f"{root}/sys/devices/system/node/node[0-9]*"), key=lambda p: int(p.rsplit("node", 1)[1])):
        mem = _read(f"{d}/meminfo") or ""
        m = re.search(r"MemTotal:\s+(\d+)\s*kB", mem)
        nodes.append(
            {
                "node": int(d.rsplit("node", 1)[1]),
                "cpulist": _read(f"{d}/cpulist"),
                "mem_bytes": int(m.group(1)) * 1024 if m else None,
            }
        )
    return nodes


def _gpu(run: Callable[[list[str]], Optional[str]]) -> tuple[Optional[str], list[dict]]:
    if shutil.which("nvidia-smi") is None:
        return None, []
    out = run(["nvidia-smi", "--query-gpu=name,memory.total,driver_version,clocks.max.sm", "--format=csv,noheader,nounits"])
    if not out:
        return None, []
    gpus = []
    for line in out.strip().splitlines():
        f = [x.strip() for x in line.split(",")]
        if len(f) >= 3:
            gpus.append({"name": f[0], "memory_mib": f[1], "driver": f[2], "max_sm_clock_mhz": f[3] if len(f) > 3 else None})
    names = sorted({g["name"] for g in gpus})
    summary = None
    if gpus:
        summary = ", ".join(f"{sum(1 for g in gpus if g['name'] == n)}x {n}" for n in names)
    return summary, gpus


def _run(argv: list[str]) -> Optional[str]:
    try:
        return subprocess.run(argv, capture_output=True, text=True, timeout=10, check=True).stdout
    except (OSError, subprocess.SubprocessError):
        return None


def collect(profile_id: str, governed: bool = False, root: str = "", run: Callable = _run, note: Optional[str] = None) -> dict:
    """Collect the host profile. `root` prefixes /proc and /sys (tests)."""
    cpuinfo = parse_cpuinfo(_read(f"{root}/proc/cpuinfo") or "")
    meminfo = parse_meminfo(_read(f"{root}/proc/meminfo") or "")
    cmdline = _read(f"{root}/proc/cmdline") or ""
    online = parse_cpulist(_read(f"{root}/sys/devices/system/cpu/online") or "")
    isolated = parse_cpulist(_read(f"{root}/sys/devices/system/cpu/isolated") or "")
    nohz = parse_cpulist(_read(f"{root}/sys/devices/system/cpu/nohz_full") or "")
    try:
        affinity = sorted(os.sched_getaffinity(0)) if not root else online
    except AttributeError:
        affinity = online
    governors = _governors(root)
    turbo = _turbo(root)
    smt_control = _read(f"{root}/sys/devices/system/cpu/smt/control")
    smt_active = _read(f"{root}/sys/devices/system/cpu/smt/active")
    thp = _read(f"{root}/sys/kernel/mm/transparent_hugepage/enabled")
    vulns = {}
    for p in sorted(glob.glob(f"{root}/sys/devices/system/cpu/vulnerabilities/*")):
        vulns[os.path.basename(p)] = _read(p)
    gpu_summary, gpus = _gpu(run)
    uname = platform.uname()

    warnings = []
    if set(governors) - {"performance"}:
        warnings.append(f"GOVERNOR_NOT_PERFORMANCE: {sorted(governors)}")
    if turbo["enabled"] is not False:
        warnings.append("TURBO_NOT_DISABLED")
    if smt_active == "1":
        warnings.append("SMT_ACTIVE")
    if not isolated:
        warnings.append("NO_ISOLCPUS")
    if cpuinfo["hypervisor"]:
        warnings.append("RUNNING_UNDER_HYPERVISOR")
    if len(cpuinfo["microcode"]) > 1:
        warnings.append("MIXED_MICROCODE")
    if thp and "[never]" not in thp and "[madvise]" not in thp:
        warnings.append("THP_ALWAYS")

    return {
        "schema": SCHEMA,
        "governed": governed,
        "hardware_profile": {
            "id": profile_id,
            "cpu_model": cpuinfo["model_name"],
            "vcpus": len(online) if online else (os.cpu_count() or 0),
            "ram_bytes": meminfo.get("MemTotal", 0),
            "gpu": gpu_summary,
        },
        "details": {
            "cpu": {
                "vendor_id": cpuinfo["vendor_id"],
                "family": cpuinfo["cpu_family"],
                "model": cpuinfo["model"],
                "stepping": cpuinfo["stepping"],
                "microcode": cpuinfo["microcode"],
                "isa_flags": cpuinfo["isa_flags"],
                "hypervisor": cpuinfo["hypervisor"],
                "online_cpus": len(online),
                "process_affinity_cpus": len(affinity),
                "governors": governors,
                "turbo": turbo,
                "smt": {"control": smt_control, "active": smt_active},
                "isolated_cpus": isolated,
                "nohz_full_cpus": nohz,
                "vulnerabilities": vulns,
            },
            "kernel": {
                "system": uname.system,
                "release": uname.release,
                "version": uname.version,
                "machine": uname.machine,
                "cmdline_isolation": parse_cmdline_isolation(cmdline),
            },
            "memory": {
                "total_bytes": meminfo.get("MemTotal"),
                "hugepages_total": meminfo.get("HugePages_Total"),
                "hugepage_size_bytes": meminfo.get("Hugepagesize"),
                "swap_total_bytes": meminfo.get("SwapTotal"),
                "transparent_hugepage": thp,
            },
            "numa": _numa(root),
            "gpus": gpus,
        },
        "warnings": warnings,
        "note": note,
        "collected_at": _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
    }
