/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity.Definitions.UnitCostRAM
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Definitions for polynomial size growth

This module contains only the semantic vocabulary for polynomial majorants,
multivariate bounds, output-size bounds, intermediate-value bounds, and
reachable-state bounds.  Constructors, closure rules, equivalence theorems,
and algorithmic proof combinators live in `Complexity.Support.SizeGrowth`.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM

universe u v w

namespace IsPolyBound

/-- Data-carrying form of a polynomial upper bound for an arbitrary natural-
valued function. -/
structure PolynomialMajorantCertificate
    {Input : Type u} (sizeOf : Input → ℕ) (cost : Input → ℕ) where
  polynomial : Polynomial ℕ
  bound : ∀ input, cost input ≤ polynomial.eval (sizeOf input)

end IsPolyBound

/-! ## Genuine multivariate polynomial bounds -/

/-- A resource counter is bounded by one multivariate polynomial with natural
coefficients in a family of named size parameters. -/
def IsMvPolynomialBound {Input : Type u} {Parameter : Type v}
    (sizes : Input → Parameter → ℕ) (cost : Input → ℕ) : Prop :=
  ∃ polynomial : MvPolynomial Parameter ℕ, ∀ input,
    cost input ≤ polynomial.eval (sizes input)

/-- Data-carrying multivariate majorant retaining the names of parameters. -/
structure MvPolynomialMajorantCertificate
    {Input : Type u} {Parameter : Type v}
    (sizes : Input → Parameter → ℕ) (cost : Input → ℕ) where
  polynomial : MvPolynomial Parameter ℕ
  bound : ∀ input, cost input ≤ polynomial.eval (sizes input)

/-- Promise-problem version of `IsMvPolynomialBound`. -/
def IsMvPolynomialBoundOn {Input : Type u} {Parameter : Type v}
    (valid : Input → Prop) (sizes : Input → Parameter → ℕ)
    (cost : Input → ℕ) : Prop :=
  ∃ polynomial : MvPolynomial Parameter ℕ, ∀ input, valid input →
    cost input ≤ polynomial.eval (sizes input)

/-- One multivariate polynomial uniformly bounds every auxiliary execution
choice. -/
def IsUniformMvPolynomialBound
    {Input : Type u} {Parameter : Type v} {Choice : Input → Type w}
    (sizes : Input → Parameter → ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∃ polynomial : MvPolynomial Parameter ℕ, ∀ input choice,
    cost input choice ≤ polynomial.eval (sizes input)

/-- Promise-restricted uniform multivariate bound. -/
def IsUniformMvPolynomialBoundOn
    {Input : Type u} {Parameter : Type v} {Choice : Input → Type w}
    (valid : (input : Input) → Choice input → Prop)
    (sizes : Input → Parameter → ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∃ polynomial : MvPolynomial Parameter ℕ, ∀ input choice,
    valid input choice →
      cost input choice ≤ polynomial.eval (sizes input)

/-! ## Polynomial output-size certificates -/

/-- A checked upper bound for the size of the output of a dependent
mathematical function. -/
structure OutputSizeCertificate
    {Input : Type u} {Output : Input → Type v}
    (outputSize : (input : Input) → Output input → ℕ)
    (function : (input : Input) → Output input) where
  bound : Input → ℕ
  output_le : ∀ input, outputSize input (function input) ≤ bound input

/-- The advertised output-size majorant is polynomial in the selected input
size. -/
def OutputSizeCertificate.IsPolynomial
    {Input : Type u} {Output : Input → Type v}
    {outputSize : (input : Input) → Output input → ℕ}
    {function : (input : Input) → Output input}
    (certificate : OutputSizeCertificate outputSize function)
    (sizeOf : Input → ℕ) : Prop :=
  IsPolyBound sizeOf certificate.bound

/-- A function has polynomial output size when it admits an explicit checked
size certificate. -/
def HasPolynomialOutputSize
    {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ)
    (outputSize : (input : Input) → Output input → ℕ)
    (function : (input : Input) → Output input) : Prop :=
  ∃ certificate : OutputSizeCertificate outputSize function,
    certificate.IsPolynomial sizeOf

/-- Representation-aware specialization using a lossless dependent output
encoding. -/
def HasPolynomialEncodedOutputSize
    {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ) (encoding : DependentEncoding Output)
    (function : (input : Input) → Output input) : Prop :=
  HasPolynomialOutputSize sizeOf encoding.size function

/-- Checked output-size majorant uniform over an auxiliary execution choice. -/
structure OutputSizeCertificateWithChoice
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (outputSize : (input : Input) → (choice : Choice input) →
      Output input choice → ℕ)
    (function : (input : Input) → (choice : Choice input) →
      Output input choice) where
  bound : Input → ℕ
  output_le : ∀ input choice,
    outputSize input choice (function input choice) ≤ bound input

/-- The choice-uniform output-size majorant is polynomial in the ordinary
input size. -/
def OutputSizeCertificateWithChoice.IsPolynomial
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {outputSize : (input : Input) → (choice : Choice input) →
      Output input choice → ℕ}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : OutputSizeCertificateWithChoice outputSize function)
    (sizeOf : Input → ℕ) : Prop :=
  IsPolyBound sizeOf certificate.bound

/-- Uniform polynomial output size for computations with auxiliary choices. -/
def HasUniformPolynomialOutputSize
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (sizeOf : Input → ℕ)
    (outputSize : (input : Input) → (choice : Choice input) →
      Output input choice → ℕ)
    (function : (input : Input) → (choice : Choice input) →
      Output input choice) : Prop :=
  ∃ certificate : OutputSizeCertificateWithChoice outputSize function,
    certificate.IsPolynomial sizeOf

/-! ## Cost bounds relative to an intermediate value -/

/-- A cost is polynomial uniformly in the original input size and the size of
a dependent intermediate value. -/
def IsPolyBoundInInputAndValueSize
    {Input : Type u} {Value : Input → Type v}
    (inputSize : Input → ℕ)
    (valueSize : (input : Input) → Value input → ℕ)
    (cost : (input : Input) → Value input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ, ∀ input value,
    cost input value ≤
      coefficient *
        (inputSize input + valueSize input value + 1) ^ exponent

/-- Choice-uniform counterpart of `IsPolyBoundInInputAndValueSize`. -/
def IsUniformPolyBoundInInputAndValueSize
    {Input : Type u} {Choice : Input → Type v}
    {Value : (input : Input) → Choice input → Type w}
    (inputSize : Input → ℕ)
    (valueSize : (input : Input) → (choice : Choice input) →
      Value input choice → ℕ)
    (cost : (input : Input) → (choice : Choice input) →
      Value input choice → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ, ∀ input choice value,
    cost input choice value ≤
      coefficient *
        (inputSize input + valueSize input choice value + 1) ^ exponent

/-! ## Reachable-state size certificates -/

namespace Cost

/-- Pure state reached after a fixed number of applications of an
instrumented transition. -/
def iterateState (step : α → Cost α) (iterations : ℕ) (initial : α) : α :=
  ((fun state ↦ (step state).value)^[iterations]) initial

end Cost

/-- A polynomial majorant for all states reached during a counted iteration. -/
structure IterateStateSizeCertificate
    {Input : Type u} {State : Input → Type v}
    (sizeOf : Input → ℕ)
    (stateSize : (input : Input) → State input → ℕ)
    (iterations : Input → ℕ)
    (step : (input : Input) → State input → Cost (State input))
    (initial : (input : Input) → State input) where
  bound : Input → ℕ
  bound_isPolynomial : IsPolyBound sizeOf bound
  state_le : ∀ input stage, stage ≤ iterations input →
    stateSize input
      (Cost.iterateState (step input) stage (initial input)) ≤ bound input

/-- A local operation count polynomial uniformly in the original input size
and the current state size. -/
abbrev IsPolyBoundInInputAndStateSize :=
  @IsPolyBoundInInputAndValueSize

end EconCSLib.OpenProblem.UnitCostRAM
