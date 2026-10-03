import json
from pathlib import Path

from arena_bench import hostprofile, report

HW_FIELDS = {"id", "cpu_model", "vcpus", "ram_bytes", "gpu"}


def _bundle(**kw):
    b = {
        "submission_id": "sub_1",
        "challenge_id": "chl_abc",
        "tier": "formal",
        "schedule_seed": "123",
        "result": {
            "hardware_profile": "cpu-epyc-32",
            "suite_revision": "r1",
            "classes": [
                {
                    "class_id": "transfer|<script>",
                    "weight_ppm": 1_000_000,
                    "runs_ns": [1_000_000_000, 1_100_000_000, 990_000_000],
                    "median_ns": 1_000_000_000,
                    "mad_ns": 10_000_000,
                    "cold_ns": 1_500_000_000,
                    "baseline_ns": 2_000_000_000,
                    "verify_median_ns": 2_500_000,
                    "proof_bytes_max": 300_000,
                    "peak_rss_bytes": 3 << 30,
                }
            ],
            "score_milli": 200_000,
            "score_ci_milli": 4_321,
            "prepare_ns": 12_000_000_000,
            "public_artifact_bytes": 64 << 20,
            "measured_by": "runner-7",
        },
        "outliers": {"transfer|<script>": {"k": 5, "flagged_indices": [1], "notes": [], "excessive": False}},
        "calibration": {"ok": False, "pre_median_ns": 1_000, "post_median_ns": 1_050, "session_drift_ppm": 50_000, "reference_ns": None, "reasons": ["SESSION_DRIFT"]},
    }
    b.update(kw)
    return b


def test_report_contents_and_escaping():
    md = report.render(_bundle())
    assert "**Score: 200.000**" in md
    assert "195.679 – 204.321" in md
    assert "2.000×" in md
    assert "1.000 s" in md and "2.500 ms" in md and "3.00 GiB" in md
    assert "<script>" not in md and "transfer\\|&lt;script&gt;" in md
    assert "not \"provably fastest\"" in md
    assert "`chl_abc`" in md and "`cpu-epyc-32`" in md
    assert "SESSION\\_DRIFT" in md and "session discarded as INFRA" in md
    assert "beyond 5·MAD" in md


def test_report_non_formal_and_no_score():
    b = _bundle(tier="experimental")
    b["result"]["score_milli"] = None
    md = report.render(b)
    assert "EXPERIMENTAL tier" in md and "Score: none" in md


def test_format_helpers():
    assert report.fmt_milli(5) == "0.005"
    assert report.fmt_ns(999) == "999 ns"
    assert report.fmt_ns(1_234_567) == "1.234 ms"
    assert report.speedup_milli(3, 2) == 1_500


def test_parsers():
    assert hostprofile.parse_cpulist("0-2,5,7-8") == [0, 1, 2, 5, 7, 8]
    assert hostprofile.parse_cpulist("") == []
    assert hostprofile.parse_cpulist("(null)") == []
    ci = hostprofile.parse_cpuinfo(
        "processor\t: 0\nmodel name\t: Foo CPU\nmicrocode\t: 0xa\nflags\t: fpu avx2 hypervisor\n\n"
        "processor\t: 1\nmodel name\t: Foo CPU\nmicrocode\t: 0xb\n"
    )
    assert ci["model_name"] == "Foo CPU" and ci["microcode"] == ["0xa", "0xb"] and ci["hypervisor"]
    assert hostprofile.parse_meminfo("MemTotal:  1024 kB\nHugePages_Total: 4\n") == {"MemTotal": 1 << 20, "HugePages_Total": 4}
    assert hostprofile.parse_cmdline_isolation("ro isolcpus=2-7 nohz_full=2-7 quiet") == {"isolcpus": "2-7", "nohz_full": "2-7"}


def _fake_root(tmp_path: Path) -> str:
    def w(rel, txt):
        p = tmp_path / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(txt)

    w("proc/cpuinfo", "processor\t: 0\nvendor_id\t: GenuineIntel\nmodel name\t: Test Xeon\nmicrocode\t: 0x2b\nflags\t: avx2 adx\n\nprocessor\t: 1\nmodel name\t: Test Xeon\nmicrocode\t: 0x2b\n")
    w("proc/meminfo", "MemTotal:       8388608 kB\n")
    w("proc/cmdline", "BOOT_IMAGE=x isolcpus=1\n")
    w("sys/devices/system/cpu/online", "0-1\n")
    w("sys/devices/system/cpu/isolated", "1\n")
    w("sys/devices/system/cpu/cpu0/cpufreq/scaling_governor", "performance\n")
    w("sys/devices/system/cpu/cpu1/cpufreq/scaling_governor", "performance\n")
    w("sys/devices/system/cpu/intel_pstate/no_turbo", "1\n")
    w("sys/devices/system/cpu/smt/active", "0\n")
    w("sys/devices/system/node/node0/cpulist", "0-1\n")
    w("sys/devices/system/node/node0/meminfo", "Node 0 MemTotal:       8388608 kB\n")
    return str(tmp_path)


def test_collect_fake_governed_host(tmp_path):
    doc = hostprofile.collect("bench-1", governed=True, root=_fake_root(tmp_path), run=lambda argv: None)
    hp = doc["hardware_profile"]
    assert set(hp) == HW_FIELDS
    assert hp == {"id": "bench-1", "cpu_model": "Test Xeon", "vcpus": 2, "ram_bytes": 8 << 30, "gpu": None}
    assert doc["details"]["cpu"]["isolated_cpus"] == [1]
    assert doc["details"]["numa"][0]["mem_bytes"] == 8 << 30
    assert doc["warnings"] == []  # performance governor, no turbo, no SMT, isolcpus set


def test_collect_real_host_shape():
    doc = hostprofile.collect("dev-host")
    assert doc["schema"] == "arena-host-profile-v1" and doc["governed"] is False
    hp = doc["hardware_profile"]
    assert set(hp) == HW_FIELDS
    assert isinstance(hp["vcpus"], int) and hp["vcpus"] > 0 and hp["ram_bytes"] > 0
    json.dumps(doc)


def test_committed_dev_host_profile():
    p = Path(__file__).resolve().parent.parent / "hardware" / "dev-host.json"
    doc = json.loads(p.read_text())
    assert doc["governed"] is False
    assert set(doc["hardware_profile"]) == HW_FIELDS
    assert doc["hardware_profile"]["id"].startswith("dev-")
