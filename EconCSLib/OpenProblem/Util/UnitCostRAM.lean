/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity.Definitions.UnitCostRAM
import EconCSLib.OpenProblem.Util.Complexity.Support.UnitCostRAM

/-!
# Unit-cost RAM compatibility facade

Foundational definitions and the optional support library are physically split
so clients can import only the layer they need.  This historical import path
re-exports both layers and therefore preserves the existing public API.
-/
