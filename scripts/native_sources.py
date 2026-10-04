"""Publish generated fixtures atomically when regression groups share a source."""
import os,tempfile
from pathlib import Path

def atomic_write_text(path,text):
    path=Path(path)
    with tempfile.NamedTemporaryFile(mode='w',encoding='utf-8',dir=path.parent,
                                     prefix=path.name+'.',suffix='.tmp',delete=False) as output:
        temporary=Path(output.name);output.write(text)
    try:os.replace(temporary,path)
    finally:
        if temporary.exists():temporary.unlink()
