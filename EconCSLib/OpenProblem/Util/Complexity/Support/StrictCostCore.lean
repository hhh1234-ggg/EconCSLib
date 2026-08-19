/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity.Definitions.StrictCostCore
import EconCSLib.OpenProblem.Util.Complexity.Support.UnitCostRAM

/-!
# Proof support for the minimal strict cost-analysis core

These lemmas connect a user-proved displayed bound to the original direct
polynomial-time predicate on the interpreter-generated operation count.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM.StrictCostCore

universe u v

theorem hasCostBound_of_hasExactCost
    {Input : Type u} {Output : Input → Type v}
    {inputEncoding : Encoding Input}
    {outputEncoding : DependentEncoding Output}
    {function : (input : Input) → Output input}
    {implementation : Implementation inputEncoding outputEncoding function}
    {formula : Input → ℕ}
    (exactCost : HasExactCost implementation formula) :
    HasCostBound implementation formula :=
  fun input ↦ (exactCost input).le

theorem machine_isPolynomialTime_of_via
    {Input : Type u} {Output : Input → Type v}
    {inputEncoding : Encoding Input}
    {outputEncoding : DependentEncoding Output}
    {function : (input : Input) → Output input}
    {implementation : Implementation inputEncoding outputEncoding function}
    {bound : Input → ℕ}
    (analysis : IsPolynomialTimeVia implementation bound) :
    implementation.IsPolynomialTime :=
  IsPolyBound.of_le analysis.2 analysis.1

theorem isPolynomialTime_iff_machine_isPolynomialTime
    {Input : Type u} {Output : Input → Type v}
    {inputEncoding : Encoding Input}
    {outputEncoding : DependentEncoding Output}
    {function : (input : Input) → Output input}
    (implementation : Implementation inputEncoding outputEncoding function) :
    IsPolynomialTime implementation ↔ implementation.IsPolynomialTime := by
  constructor
  · rintro ⟨bound, analysis⟩
    exact machine_isPolynomialTime_of_via analysis
  · intro polynomialTime
    exact ⟨executionCost implementation, fun _ ↦ le_rfl, polynomialTime⟩

end EconCSLib.OpenProblem.UnitCostRAM.StrictCostCore
