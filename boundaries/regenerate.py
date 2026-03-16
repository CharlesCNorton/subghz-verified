from __future__ import annotations

import argparse
import csv
import os
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def windows_to_wsl(path: Path) -> str:
    drive = path.drive.rstrip(":").lower()
    tail = path.as_posix().split(":", 1)[1]
    return f"/mnt/{drive}{tail}"


def run_wsl(script: str) -> subprocess.CompletedProcess[str]:
    distro = os.environ.get("SUBGHZ_WSL_DISTRO", "Ubuntu")
    command = [
        "powershell.exe",
        "-NoProfile",
        "-Command",
        f"wsl -d {distro} -- bash -c {shlex.quote(script)}",
    ]
    build_dir = repo_root() / "boundaries" / "_build"
    build_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=build_dir) as temp_dir:
        stdout_path = Path(temp_dir) / "stdout.txt"
        stderr_path = Path(temp_dir) / "stderr.txt"
        with stdout_path.open("w", encoding="utf-8") as stdout_handle, stderr_path.open(
            "w", encoding="utf-8"
        ) as stderr_handle:
            result = subprocess.run(command, stdout=stdout_handle, stderr=stderr_handle, text=True)
        stdout = stdout_path.read_text(encoding="utf-8")
        stderr = stderr_path.read_text(encoding="utf-8")
        if result.returncode != 0:
            raise subprocess.CalledProcessError(result.returncode, command, output=stdout, stderr=stderr)
        return subprocess.CompletedProcess(command, result.returncode, stdout, stderr)


def ensure_runner(root: Path) -> Path:
    build_dir = root / "boundaries" / "_build"
    build_dir.mkdir(parents=True, exist_ok=True)
    runner = build_dir / "atlas_runner.opt"
    build_dir_wsl = windows_to_wsl(build_dir)
    script = "\n".join(
        [
            "set -e",
            'export PATH="${SUBGHZ_OCAML_BIN:-$HOME/.opam/default/bin}:/usr/local/bin:/usr/bin:/bin"',
            'export OPAMROOT="${SUBGHZ_OPAMROOT:-$HOME/.opam}"',
            f"mkdir -p {shlex.quote(build_dir_wsl)}",
            f"cp {shlex.quote(windows_to_wsl(root / 'burst_detector_extracted.mli'))} {shlex.quote(build_dir_wsl + '/burst_detector_extracted.mli')}",
            f"cp {shlex.quote(windows_to_wsl(root / 'burst_detector_extracted.ml'))} {shlex.quote(build_dir_wsl + '/burst_detector_extracted.ml')}",
            f"cp {shlex.quote(windows_to_wsl(root / 'boundaries' / 'atlas_runner.ml'))} {shlex.quote(build_dir_wsl + '/atlas_runner.ml')}",
            f"cd {shlex.quote(build_dir_wsl)}",
            "ocamlopt -c burst_detector_extracted.mli",
            "ocamlopt -c burst_detector_extracted.ml",
            "ocamlopt burst_detector_extracted.cmx atlas_runner.ml -o atlas_runner.opt",
        ]
    )
    run_wsl(script)
    return runner


def parse_cases(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def parse_regimes(spec: str) -> list[str]:
    return [item for item in spec.split(";") if item]


def parse_kv_output(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or "=" not in line:
            continue
        key, value = line.split("=", 1)
        result[key] = value
    return result


def run_case(
    runner: Path,
    file_path: Path,
    descriptor: str,
    crop_window_pairs: str,
    crop_threshold: str,
    crop_pad_windows: str,
    regimes: str,
) -> dict[str, str]:
    runner_wsl = windows_to_wsl(runner)
    file_wsl = windows_to_wsl(file_path)
    regime_args = " ".join(shlex.quote(item) for item in parse_regimes(regimes))
    script = "\n".join(
        [
            "set -e",
            'export PATH="${SUBGHZ_OCAML_BIN:-$HOME/.opam/default/bin}:/usr/local/bin:/usr/bin:/bin"',
            'export OPAMROOT="${SUBGHZ_OPAMROOT:-$HOME/.opam}"',
            f"{shlex.quote(runner_wsl)} --crop-window-pairs {crop_window_pairs} --crop-threshold {crop_threshold} --crop-pad-windows {crop_pad_windows} phasepathfast {shlex.quote(descriptor)} {shlex.quote(file_wsl)} {regime_args}",
        ]
    )
    output = run_wsl(script)
    return parse_kv_output(output.stdout)


def build_row(case: dict[str, str], data: dict[str, str], include_case_id: bool) -> dict[str, str]:
    row: dict[str, str] = {}
    if include_case_id:
        row["case_id"] = case["case_id"]
    row["family_id"] = case["family_id"]
    if "key" in case:
        row["key"] = case["key"]
    row["descriptor"] = case["descriptor"]
    row["file"] = case["file"]
    row["crop_applied"] = data.get("CROP_APPLIED", "false")
    row["crop_window_pairs"] = data.get("CROP_WINDOW_PAIRS", case["crop_window_pairs"])
    row["crop_threshold"] = data.get("CROP_THRESHOLD", case["crop_threshold"])
    row["crop_pad_windows"] = data.get("CROP_PAD_WINDOWS", case["crop_pad_windows"])
    row["crop_stop_byte"] = data.get("CROP_STOP_BYTE", "")
    row["regimes"] = case["regimes"]
    row["boundary_kinds"] = data.get("BOUNDARY_KINDS", "")
    row["class_transitions"] = data.get("CLASS_TRANSITIONS", "")
    row["phase_transitions"] = data.get("PHASE_TRANSITIONS", "")
    for index in range(4):
        row[f"regime_{index}"] = data.get(f"REGIME_{index}", "")
        row[f"frame_hex_{index}"] = data.get(f"FRAME_HEX_{index}", "")
        row[f"frame_bits_len_{index}"] = data.get(f"FRAME_BITS_LEN_{index}", "")
        row[f"class_digest_{index}"] = data.get(f"CLASS_DIGEST_{index}", "")
    row["notes"] = case["notes"]
    return row


def frame_hex_seq(row: dict[str, str]) -> str:
    start = 0
    values: list[str] = []
    while row.get(f"regime_{start}", ""):
        values.append(row.get(f"frame_hex_{start}", ""))
        start += 1
    return "[" + ",".join(values) + "]"


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, str]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    root = repo_root()
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--live-root",
        default=os.environ.get(
            "SUBGHZ_LIVE_CAPTURE_ROOT",
            str(root / "boundaries" / "live_captures"),
        ),
    )
    parser.add_argument("--skip-corpus", action="store_true")
    parser.add_argument("--skip-live", action="store_true")
    args = parser.parse_args()

    boundaries_dir = root / "boundaries"
    runner = ensure_runner(root)

    corpus_rows: list[dict[str, str]] = []
    if args.skip_corpus:
        with (boundaries_dir / "manifest.csv").open(newline="", encoding="utf-8") as handle:
            corpus_rows = list(csv.DictReader(handle))
    else:
        corpus_cases = parse_cases(boundaries_dir / "corpus_cases.csv")
        for case in corpus_cases:
            data = run_case(
                runner,
                root / case["file"],
                case["descriptor"],
                case["crop_window_pairs"],
                case["crop_threshold"],
                case["crop_pad_windows"],
                case["regimes"],
            )
            corpus_rows.append(build_row(case, data, include_case_id=False))

    corpus_fieldnames = [
        "family_id",
        "key",
        "descriptor",
        "file",
        "crop_applied",
        "crop_window_pairs",
        "crop_threshold",
        "crop_pad_windows",
        "crop_stop_byte",
        "regimes",
        "boundary_kinds",
        "class_transitions",
        "phase_transitions",
        "regime_0",
        "frame_hex_0",
        "frame_bits_len_0",
        "class_digest_0",
        "regime_1",
        "frame_hex_1",
        "frame_bits_len_1",
        "class_digest_1",
        "regime_2",
        "frame_hex_2",
        "frame_bits_len_2",
        "class_digest_2",
        "regime_3",
        "frame_hex_3",
        "frame_bits_len_3",
        "class_digest_3",
        "notes",
    ]
    if not args.skip_corpus:
        write_csv(boundaries_dir / "manifest.csv", corpus_fieldnames, corpus_rows)

    live_root = Path(args.live_root)
    live_rows: list[dict[str, str]] = []
    if args.skip_live:
        if (boundaries_dir / "live_manifest.csv").exists():
            with (boundaries_dir / "live_manifest.csv").open(newline="", encoding="utf-8") as handle:
                live_rows = list(csv.DictReader(handle))
    else:
        live_cases = parse_cases(boundaries_dir / "live_cases.csv")
        if live_root.exists():
            for case in live_cases:
                data = run_case(
                    runner,
                    live_root / case["file"],
                    case["descriptor"],
                    case["crop_window_pairs"],
                    case["crop_threshold"],
                    case["crop_pad_windows"],
                    case["regimes"],
                )
                live_rows.append(build_row(case, data, include_case_id=True))

    live_fieldnames = [
        "case_id",
        "family_id",
        "descriptor",
        "file",
        "crop_applied",
        "crop_window_pairs",
        "crop_threshold",
        "crop_pad_windows",
        "crop_stop_byte",
        "regimes",
        "boundary_kinds",
        "class_transitions",
        "phase_transitions",
        "regime_0",
        "frame_hex_0",
        "frame_bits_len_0",
        "class_digest_0",
        "regime_1",
        "frame_hex_1",
        "frame_bits_len_1",
        "class_digest_1",
        "regime_2",
        "frame_hex_2",
        "frame_bits_len_2",
        "class_digest_2",
        "regime_3",
        "frame_hex_3",
        "frame_bits_len_3",
        "class_digest_3",
        "notes",
    ]
    if not args.skip_live:
        write_csv(boundaries_dir / "live_manifest.csv", live_fieldnames, live_rows)

    corpus_by_family = {row["family_id"]: row for row in corpus_rows}
    comparison_rows: list[dict[str, str]] = []
    for live_row in live_rows:
        corpus_row = corpus_by_family[live_row["family_id"]]
        same_boundary_kinds = live_row["boundary_kinds"] == corpus_row["boundary_kinds"]
        same_class_transitions = live_row["class_transitions"] == corpus_row["class_transitions"]
        same_phase_transitions = live_row["phase_transitions"] == corpus_row["phase_transitions"]
        same_frame_hex_seq = frame_hex_seq(live_row) == frame_hex_seq(corpus_row)
        if same_boundary_kinds and same_frame_hex_seq:
            comparison_label = "exact_match"
        elif same_boundary_kinds:
            comparison_label = "same_boundary_kinds"
        elif same_phase_transitions:
            comparison_label = "same_phase_mask"
        elif same_class_transitions:
            comparison_label = "same_class_mask"
        else:
            comparison_label = "divergent"
        comparison_rows.append(
            {
                "case_id": live_row["case_id"],
                "family_id": live_row["family_id"],
                "corpus_file": corpus_row["file"],
                "live_file": live_row["file"],
                "regimes": live_row["regimes"],
                "corpus_boundary_kinds": corpus_row["boundary_kinds"],
                "live_boundary_kinds": live_row["boundary_kinds"],
                "corpus_class_transitions": corpus_row["class_transitions"],
                "live_class_transitions": live_row["class_transitions"],
                "corpus_phase_transitions": corpus_row["phase_transitions"],
                "live_phase_transitions": live_row["phase_transitions"],
                "corpus_frame_hex_seq": frame_hex_seq(corpus_row),
                "live_frame_hex_seq": frame_hex_seq(live_row),
                "same_boundary_kinds": str(same_boundary_kinds).lower(),
                "same_class_transitions": str(same_class_transitions).lower(),
                "same_phase_transitions": str(same_phase_transitions).lower(),
                "same_frame_hex_seq": str(same_frame_hex_seq).lower(),
                "comparison_label": comparison_label,
                "notes": live_row["notes"],
            }
        )

    comparison_fieldnames = [
        "case_id",
        "family_id",
        "corpus_file",
        "live_file",
        "regimes",
        "corpus_boundary_kinds",
        "live_boundary_kinds",
        "corpus_class_transitions",
        "live_class_transitions",
        "corpus_phase_transitions",
        "live_phase_transitions",
        "corpus_frame_hex_seq",
        "live_frame_hex_seq",
        "same_boundary_kinds",
        "same_class_transitions",
        "same_phase_transitions",
        "same_frame_hex_seq",
        "comparison_label",
        "notes",
    ]
    write_csv(boundaries_dir / "live_vs_corpus.csv", comparison_fieldnames, comparison_rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
