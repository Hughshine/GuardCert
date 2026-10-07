#!/usr/bin/env python3
"""Fetch the checksum-pinned release into this workspace; never install it."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import urllib.request


def main(archive_path=None) -> None:
    root = Path(__file__).resolve().parents[1]
    pin = json.loads((root / "toolchain.lock.json").read_text())["compcert"]
    destination = root / "vendor" / "CompCert"
    stamp = destination / ".guard-source.json"
    if destination.exists():
        if not stamp.exists() or json.loads(stamp.read_text()) != pin:
            raise SystemExit("Existing CompCert directory has no matching source pin.")
        print(f"Using pinned CompCert {pin['tag']} ({pin['commit']}).")
        return

    destination.parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent) as staging:
        archive = Path(staging) / "source.tar.gz"
        if archive_path is None:
            with urllib.request.urlopen(pin["archive_url"], timeout=60) as response:
                with archive.open("wb") as output:
                    shutil.copyfileobj(response, output)
        else:
            shutil.copyfile(archive_path, archive)
        digest = hashlib.sha256(archive.read_bytes()).hexdigest()
        if digest != pin["archive_sha256"]:
            raise SystemExit(f"CompCert archive checksum mismatch: {digest}")
        unpacked = Path(staging) / "source"
        unpacked.mkdir()
        with tarfile.open(archive) as bundle:
            # Strip the release's top-level directory and accept regular files.
            for member in bundle.getmembers():
                parts = Path(member.name).parts[1:]
                if not parts:
                    continue
                if any(part in ("..", "/") for part in parts):
                    raise SystemExit("Invalid archive path")
                target = unpacked.joinpath(*parts)
                if member.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                elif member.isfile():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with bundle.extractfile(member) as source, target.open("wb") as output:
                        shutil.copyfileobj(source, output)
                    target.chmod(member.mode & 0o777)
                else:
                    raise SystemExit(f"Unsupported archive entry: {member.name}")
        (unpacked / ".guard-source.json").write_text(json.dumps(pin, indent=2) + "\n")
        unpacked.rename(destination)
    print(f"Fetched CompCert {pin['tag']} ({pin['commit']}).")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path,
                        help="use a local release archive, checking the same pinned checksum")
    main(parser.parse_args().archive)
