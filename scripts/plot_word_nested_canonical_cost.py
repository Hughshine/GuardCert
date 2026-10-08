"""Export paired complete-call cost ratios from the frozen timing checkpoint."""
import argparse
import json
import os
from pathlib import Path
import shutil
import statistics

from audit_interface_clight import ROOT, sha
import measure_word_nested_canonical_cost as cost

os.environ["MPLCONFIGDIR"] = "/tmp/guard-canonical-alias-cost-mpl"
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

WORK = ROOT / "build/multi-word-nested-canonical/cost-plot-v1"
ASSET = ROOT / "paper/figures/canonical-alias-cost.pdf"
LABELS = ["2 by 3 accepted", "8 by 8 accepted", "RHS word wrap", "Array alias refusal",
          "Start refusal", "Header alias refusal", "Cap refusal", "Outer empty", "Child empty"]


def validate(work=WORK):
    measured = cost.validate()
    report = json.loads((work / "report.json").read_text())
    assert report["status"] == "exported" and report["timing_report_sha256"] == sha(cost.WORK / "report.json")
    assert report["samples"] == measured["samples"]
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    return report


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    WORK = args.work.resolve()
    assert WORK.is_relative_to(ROOT / "build/multi-word-nested-canonical")
    if args.validate or (WORK / "report.json").exists():
        validate(WORK)
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    assert not WORK.exists() and not ASSET.exists(), "Use new plot/asset paths for a successor"
    measured = cost.validate()
    samples = [json.loads(line) for line in (cost.WORK / "samples.jsonl").read_text().splitlines()]
    values = {(s["profile"], s["case"], s["mode"], s["round"]): s["ns_per_call"] for s in samples}
    plt.rcParams.update({"font.size": 9, "axes.titlesize": 10, "svg.hashsalt": "guardcert-canonical-alias-cost"})
    fig, axes = plt.subplots(1, 3, figsize=(7.4, 4.4), sharey=True)
    WORK.mkdir()
    statistics_used = {}
    for axis, profile in zip(axes, measured["profiles"]):
        statistics_used[profile] = {}
        for mode, color, marker, offset, label in [("memo", "#0072B2", "o", -0.13, "Original alias scan"),
                                                   ("canonical", "#D55E00", "s", 0.13, "Canonical alias scan")]:
            medians, lower, upper = [], [], []
            for case in measured["cases"]:
                ratios = [values[(profile, case, mode, r)] / values[(profile, case, "source", r)]
                          for r in range(cost.ROUNDS)]
                median = statistics.median(ratios)
                q1, _q2, q3 = statistics.quantiles(ratios, n=4, method="inclusive")
                assert median == measured["summaries"][profile][case][mode]["median_paired_cost_over_source"]
                medians.append(median)
                lower.append(median - q1)
                upper.append(q3 - median)
                statistics_used[profile].setdefault(case, {})[mode] = {"median": median, "q1": q1, "q3": q3}
            axis.errorbar(medians, [i + offset for i in range(len(LABELS))], xerr=[lower, upper],
                          fmt=marker, color=color, markersize=4, capsize=2, lw=0.9, label=label)
        axis.axvline(1, color="0.35", ls="--", lw=0.9)
        axis.set_xscale("log")
        axis.set_xlim(0.8, 350)
        axis.set_xticks([1, 10, 100], labels=["1", "10", "100"])
        axis.grid(axis="x", which="major", color="0.88", lw=0.6)
        axis.set_title({"row": "Row", "column": "Column", "row-variable": "Row, parameter stride"}[profile])
        axis.set_xlabel("Cost / source (log scale)")
        axis.spines[["top", "right"]].set_visible(False)
    axes[0].set_yticks(range(len(LABELS)), labels=LABELS)
    axes[0].invert_yaxis()
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", bbox_to_anchor=(0.62, 0.99), ncols=2, frameon=False)
    fig.text(0.5, 0.035, "Lower is faster; intervals are paired-ratio IQRs. Selected warm inputs; cap 8.",
             ha="center", fontsize=8)
    fig.subplots_adjust(left=0.26, right=0.985, top=0.85, bottom=0.16, wspace=0.12)
    for extension in ["pdf", "svg", "png"]:
        fig.savefig(WORK / ("complete-call-cost." + extension), dpi=240,
                    metadata={"Creator": "GuardCert measured-cost plot"} if extension == "pdf" else None)
    plt.close(fig)
    ASSET.parent.mkdir(exist_ok=True)
    shutil.copyfile(WORK / "complete-call-cost.pdf", ASSET)
    bindings = {cost.WORK / "report.json": sha(cost.WORK / "report.json"),
                cost.WORK / "samples.jsonl": sha(cost.WORK / "samples.jsonl"),
                Path(__file__): sha(Path(__file__)), ASSET: sha(ASSET)}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "exported", "timing_report_sha256": sha(cost.WORK / "report.json"),
              "samples": measured["samples"], "statistics": statistics_used,
              "matplotlib": matplotlib.__version__, "scientific_plot_export": True,
              "representative_workload_speedup_claim": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    with (WORK / "report.json").open("x") as out:
        out.write(json.dumps(report, indent=2) + "\n")
    validate(WORK)
    print(json.dumps({"status": "exported", "paper_asset": str(ASSET.relative_to(ROOT)),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
