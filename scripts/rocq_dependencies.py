"""Compile an owned Rocq dependency closure in dependency order."""
import subprocess
from pathlib import Path


def compile_closure(root, sources, flags, work, directories, force=False):
    root, work = Path(root), Path(work)
    allowed = [root / directory for directory in directories]
    graph, discovered = {}, set()
    requested = [(root / source).resolve() for source in sources]
    pending = list(requested)
    dependency_output, warnings = [], []

    def owned(source):
        return any(source.is_relative_to(directory) for directory in allowed)

    def absolute(filename):
        return (root / filename).resolve()

    while pending:
        batch = list(dict.fromkeys(pending))
        discovered.update(batch)
        result = subprocess.run(["rocq", "dep", *flags, *map(str, batch)], cwd=root,
                                capture_output=True, text=True)
        dependency_output.append(result.stdout)
        warnings.append(result.stderr)
        (work / "dependencies.txt").write_text("".join(dependency_output))
        (work / "dependency-warnings.txt").write_text("".join(warnings))
        if result.returncode:
            raise SystemExit("Rocq dependency discovery failed; see dependency-warnings.txt")
        pending = []
        for line in result.stdout.splitlines():
            if ": " not in line:
                continue
            outputs, dependencies = line.split(": ", 1)
            primary = outputs.split()[0]
            if not primary.endswith(".vo"):
                continue
            source = absolute(primary).with_suffix(".v")
            deps = [absolute(name) for name in dependencies.split() if name.endswith(".vo")]
            graph[source] = deps
            for obj in deps:
                dependency = obj.with_suffix(".v")
                if owned(dependency) and dependency.exists() and dependency not in discovered:
                    pending.append(dependency)
    seen, order = set(), []

    def visit(source):
        if source in seen:
            return
        seen.add(source)
        for obj in graph.get(source, []):
            dependency = obj.with_suffix(".v")
            if dependency in graph:
                visit(dependency)
        order.append(source)

    for source in requested:
        visit(source)
    logs = []
    for source in order:
        obj = source.with_suffix(".vo")
        inputs = [source, *graph[source]]
        fresh = obj.exists() and all(p.exists() and p.stat().st_mtime <= obj.stat().st_mtime for p in inputs)
        if fresh and not force:
            continue
        log = work / (source.stem + ".log")
        result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=root,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        log.write_text(result.stdout)
        logs.append(f"Compiling {source.relative_to(root)}\n{result.stdout}")
        (work / "proof.log").write_text("\n".join(logs))
        if result.returncode:
            raise SystemExit(f"Rocq compilation failed: {source.relative_to(root)}; see {log}")
        print(f"Compiled {source.relative_to(root)}", flush=True)
    return [str(source.relative_to(root)) for source in order]
