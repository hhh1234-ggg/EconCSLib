/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity.Definitions.UnitCostRAMMachine

/-!
# Proof support for fixed-representation unit-cost RAM certificates

All semantic structures and predicates are defined in the definition-only
module.  This module contains only named theorems and their proofs.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM

universe u v w

noncomputable section

namespace FixedEncodingRAMImplementation

variable {Input : Type u} {Output : Input → Type v}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {function : (input : Input) → Output input}

@[simp] theorem standardResourceCount_localSteps
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function)
    (input : Input) :
    implementation.standardResourceCount .localSteps input =
      implementation.operationCount input := rfl

theorem isPolynomialTime_iff_stepsResource
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function) :
    implementation.IsPolynomialTime ↔
      implementation.HasPolynomialResource
        (fun _ execution ↦ ProfiledCost.steps execution) :=
  Iff.rfl

theorem isPolynomialTime_iff_standardLocalSteps
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function) :
    implementation.IsPolynomialTime ↔
      implementation.HasPolynomialStandardResource .localSteps :=
  Iff.rfl

end FixedEncodingRAMImplementation

namespace StrictRAMComputableInPolyTime

variable {Input : Type u} {Output : Input → Type v}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {function : (input : Input) → Output input}

theorem toImplementation_isPolynomialTime
    (certificate : StrictRAMComputableInPolyTime
      inputEncoding outputEncoding function) :
    certificate.toImplementation.IsPolynomialTime :=
  ⟨certificate.coefficient, certificate.exponent, certificate.time_bound⟩

end StrictRAMComputableInPolyTime

/-- The bundled strict certificate is exactly the combination of an exact
fixed-encoding implementation and the separate polynomial-majorant property. -/
theorem nonempty_strictRAMComputableInPolyTime_iff
    {Input : Type u} {Output : Input → Type v}
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (function : (input : Input) → Output input) :
    Nonempty (StrictRAMComputableInPolyTime
      inputEncoding outputEncoding function) ↔
      ∃ implementation : FixedEncodingRAMImplementation
        inputEncoding outputEncoding function,
        implementation.IsPolynomialTime := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.toImplementation,
      certificate.toImplementation_isPolynomialTime⟩
  · rintro ⟨implementation, coefficient, exponent, timeBound⟩
    exact ⟨{
      program := implementation.program
      fuel := implementation.fuel
      coefficient := coefficient
      exponent := exponent
      correct := implementation.correct
      time_bound := timeBound }⟩

namespace FixedEnvironmentRAMImplementation

variable {Input : Type u} {Choice : Input → Type v}
  {Output : (input : Input) → Choice input → Type w}
  {inputEncoding : Encoding Input}
  {outputEncoding : ChoiceDependentEncoding Output}
  {ExternalOperation : Type*}
  {environment : (input : Input) →
    Choice input → MachineEnvironment ExternalOperation}
  {function : (input : Input) →
    (choice : Choice input) → Output input choice}

@[simp] theorem standardResourceCount_localSteps
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function)
    (input : Input) (choice : Choice input) :
    implementation.standardResourceCount .localSteps input choice =
      implementation.operationCount input choice := rfl

theorem isPolynomialTime_iff_stepsResource
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function) :
    implementation.IsPolynomialTime ↔
      implementation.HasPolynomialResource
        (fun _ _ execution ↦ ProfiledCost.steps execution) :=
  Iff.rfl

theorem isPolynomialTime_iff_standardLocalSteps
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function) :
    implementation.IsPolynomialTime ↔
      implementation.HasPolynomialStandardResource .localSteps :=
  Iff.rfl

end FixedEnvironmentRAMImplementation

namespace FixedEncodingRAMSearchImplementation

variable {Input : Type u} {Output : Input → Type v}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {valid : Input → Prop}
  {solution : (input : Input) → Output input → Prop}

@[simp] theorem standardResourceCount_localSteps
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution)
    (input : Input) :
    implementation.standardResourceCount .localSteps input =
      implementation.operationCount input := rfl

theorem isPolynomialTimeOn_iff_stepsResource
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution) :
    implementation.IsPolynomialTimeOn ↔
      implementation.HasPolynomialResourceOn
        (fun _ execution ↦ ProfiledCost.steps execution) :=
  Iff.rfl

theorem isPolynomialTimeOn_iff_standardLocalSteps
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution) :
    implementation.IsPolynomialTimeOn ↔
      implementation.HasPolynomialStandardResourceOn .localSteps :=
  Iff.rfl

end FixedEncodingRAMSearchImplementation

namespace StrictRAMSearchableInPolyTime

variable {Input : Type u} {Output : Input → Type v}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {valid : Input → Prop}
  {solution : (input : Input) → Output input → Prop}

theorem toImplementation_isPolynomialTimeOn
    (certificate : StrictRAMSearchableInPolyTime
      inputEncoding outputEncoding valid solution) :
    certificate.toImplementation.IsPolynomialTimeOn :=
  ⟨certificate.coefficient, certificate.exponent, certificate.time_bound⟩

end StrictRAMSearchableInPolyTime

theorem nonempty_strictRAMSearchableInPolyTime_iff
    {Input : Type u} {Output : Input → Type v}
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (valid : Input → Prop)
    (solution : (input : Input) → Output input → Prop) :
    Nonempty (StrictRAMSearchableInPolyTime
      inputEncoding outputEncoding valid solution) ↔
      ∃ implementation : FixedEncodingRAMSearchImplementation
        inputEncoding outputEncoding valid solution,
        implementation.IsPolynomialTimeOn := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.toImplementation,
      certificate.toImplementation_isPolynomialTimeOn⟩
  · rintro ⟨implementation, coefficient, exponent, timeBound⟩
    exact ⟨{
      program := implementation.program
      fuel := implementation.fuel
      coefficient := coefficient
      exponent := exponent
      correct := implementation.correct
      time_bound := timeBound }⟩

namespace StrictRAMComputableInPolyTimeWithFixedEnvironment

theorem toImplementation_isPolynomialTime
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {ExternalOperation : Type*}
    {environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithFixedEnvironment
      inputEncoding outputEncoding ExternalOperation environment function) :
    certificate.toImplementation.IsPolynomialTime :=
  ⟨certificate.coefficient, certificate.exponent, certificate.time_bound⟩

end StrictRAMComputableInPolyTimeWithFixedEnvironment

theorem nonempty_strictRAMComputableInPolyTimeWithFixedEnvironment_iff
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (inputEncoding : Encoding Input)
    (outputEncoding : ChoiceDependentEncoding Output)
    (ExternalOperation : Type*)
    (environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation)
    (function : (input : Input) → (choice : Choice input) →
      Output input choice) :
    Nonempty (StrictRAMComputableInPolyTimeWithFixedEnvironment
      inputEncoding outputEncoding ExternalOperation environment function) ↔
      ∃ implementation : FixedEnvironmentRAMImplementation
        inputEncoding outputEncoding ExternalOperation environment function,
        implementation.IsPolynomialTime := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.toImplementation,
      certificate.toImplementation_isPolynomialTime⟩
  · rintro ⟨implementation, coefficient, exponent, timeBound⟩
    exact ⟨{
      choice_nonempty := implementation.choice_nonempty
      program := implementation.program
      fuel := implementation.fuel
      coefficient := coefficient
      exponent := exponent
      correct := implementation.correct
      time_bound := timeBound }⟩


end

end EconCSLib.OpenProblem.UnitCostRAM

