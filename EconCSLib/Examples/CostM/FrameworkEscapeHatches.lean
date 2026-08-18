/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity

/-!
# Regression tests for complexity-model escape hatches

These named regression declarations make three trust boundaries executable
and reviewable:

1. a permissive decoder cannot replace the function computed by a strict
   program, because the machine must emit the fixed canonical encoding;
2. `Cost.pure` and an external callback are trusted accounting boundaries;
3. strict search reductions expose canonical intermediate words, so their
   stages compose without an uncharged decoder/normalizer.
-/

namespace EconCSLib.Examples.CostM.FrameworkEscapeHatches

open EconCSLib.OpenProblem
open EconCSLib.OpenProblem.UnitCostRAM
open EconCSLib.OpenProblem.EconCSBench

noncomputable section

/-! ## A decoder alias cannot hide the computed function -/

def unitEncoding : Encoding Unit where
  encode _ := [.bit false]
  decode
    | [.bit false] => some ()
    | _ => none
  decode_encode _ := rfl

/-- This deliberately permissive decoder accepts `[]` as an alias for
`true`.  Its canonical encoding of `true` is nevertheless `[.bit true]`. -/
def decoderAliasBoolEncoding : Encoding Bool where
  encode value := [.bit value]
  decode
    | [] => some true
    | [.bit value] => some value
    | _ => none
  decode_encode value := by cases value <;> rfl

theorem decoder_alias_is_accepted :
    decoderAliasBoolEncoding.decode [] = some true := rfl

theorem decoder_alias_is_not_canonical :
    decoderAliasBoolEncoding.encode true ≠ [] := by decide

/-- Even with the permissive decoder above, a strict certificate for the
constant-`true` function must physically emit the canonical bit word.  The
empty alias cannot be used as a zero-work output. -/
theorem strict_certificate_emits_canonical_output
    (certificate : UnitCostRAM.StrictRAMComputableInPolyTime
      unitEncoding decoderAliasBoolEncoding.dependent (fun _ : Unit => true)) :
    ∃ finalState,
      (run (closedEnvironment fun _ => false)
          certificate.program (certificate.fuel ())
          (unitEncoding.encode ())).ret =
        .halted [.bit true] finalState := by
  simpa [Encoding.dependent, decoderAliasBoolEncoding] using
    certificate.correct ()

/-! ## Trusted accounting is visibly weaker than machine enforcement -/

/-- `Cost.pure` can wrap an arbitrary Lean computation while reporting zero
operations.  This is why `CostedImplementation` is only a trusted accounting
interface and is not used by the strict complexity predicates. -/
def hiddenFactorialCost (input : ℕ) : Cost ℕ :=
  Cost.pure input.factorial

theorem hiddenFactorialCost_ops_eq_zero (input : ℕ) :
    (hiddenFactorialCost input).ops = 0 := rfl

inductive CallbackOperation
  | apply

/-- An arbitrary Lean callback installed as a unit-cost oracle boundary. -/
def callbackEnvironment (callback : Word → Word) :
    MachineEnvironment CallbackOperation where
  external
    | .apply, [word] => [callback word]
    | _, _ => []
  randomTape _ := false

/-- The callback body is unrestricted at this boundary. -/
theorem callbackEnvironment_external_apply
    (callback : Word → Word) (input : Word) :
    (callbackEnvironment callback).external .apply [input] =
      [callback input] := rfl

/-- Only the query and the transferred words occur in the machine's local
account.  The callback's internal Lean evaluation is intentionally absent. -/
theorem oracleQueryTransfer_one_one_steps :
    (ResourceCounts.oracleQueryTransfer 1 1).steps = 3 := rfl

theorem oracleQueryTransfer_one_one_queries :
    (ResourceCounts.oracleQueryTransfer 1 1).oracleQueries = 1 := rfl

/-! ## Reduction stages normalize to fixed canonical words -/

/-- Type-checking this generic regression theorem ensures that the first
stage of every strict search reduction exposes the exact target encoding,
rather than merely an arbitrary word list accepted by its decoder. -/
theorem reduction_first_stage_is_operationally_composable
    {source target : SearchProblem}
    {sourceInputEncoding : Encoding source.Input}
    {sourceOutputEncoding : DependentEncoding source.Output}
    {targetInputEncoding : Encoding target.Input}
    {targetOutputEncoding : DependentEncoding target.Output}
    (reduction : FixedEncodingPolynomialSearchReduction source target
      sourceInputEncoding sourceOutputEncoding
      targetInputEncoding targetOutputEncoding)
    (input : source.Input) :
    ∃ finalState,
      (run (closedEnvironment fun _ => false)
          reduction.inputProgram.program
          (reduction.inputProgram.fuel input)
          (sourceInputEncoding.encode input)).ret =
        .halted (targetInputEncoding.encode (reduction.mapInput input))
          finalState :=
  reduction.inputProgram_outputs_canonical input

end

end EconCSLib.Examples.CostM.FrameworkEscapeHatches
