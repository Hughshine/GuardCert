from pathlib import Path

root = Path(__file__).resolve().parents[1]
for directory in (root / 'theories',):
    for pattern in ('*.vo', '*.vos', '*.vok', '*.glob', '.*.aux', '.lia.cache'):
        for path in directory.glob(pattern):
            path.unlink()
