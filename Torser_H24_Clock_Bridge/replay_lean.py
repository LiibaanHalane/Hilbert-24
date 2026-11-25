#!/usr/bin/env python3
"""Rebuild the portable Lean source package with Lean 4.19.0."""
from pathlib import Path
import os, shutil, subprocess
root=Path(__file__).resolve().parent
lean=os.environ.get('TORSER_LEAN') or shutil.which('lean')
if not lean: raise SystemExit('Set TORSER_LEAN to a Lean 4.19.0 executable.')
formal=root/'formal/lean'
env=dict(os.environ,LEAN_PATH=str(formal))
for name in ('Hilbert24_Calibrated_Policy','H24_Operational_Bridge','H24_Operational_Converse','H24_Clock_Credit','H24_Operational_Dependencies'):
    subprocess.run([lean,'-o',name+'.olean',name+'.lean'],cwd=formal,env=env,check=True)
