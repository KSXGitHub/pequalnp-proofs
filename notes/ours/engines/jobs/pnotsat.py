#!/usr/bin/env python3
"""Dispatcher entry point for one exact-synthesis query; the work is in
/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnot/notsat.py
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

NOTSAT = Path("/tmp/claude-0/-home-user-pequalnp-proofs/"
              "731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnot/notsat.py")

spec = importlib.util.spec_from_file_location("notsat", str(NOTSAT))
assert spec and spec.loader
mod = importlib.util.module_from_spec(spec)
sys.modules["notsat"] = mod
spec.loader.exec_module(mod)

sys.exit(mod.main(sys.argv[1:]))
