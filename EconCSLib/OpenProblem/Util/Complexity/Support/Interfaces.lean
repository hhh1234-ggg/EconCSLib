/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity.Definitions.Interfaces
import EconCSLib.OpenProblem.Util.Complexity.Support.SizeGrowth
import EconCSLib.OpenProblem.Util.Complexity.Support.StrictCostCore
import EconCSLib.OpenProblem.Util.Complexity.Support.UnitCostRAMMachine

/-!
# Support library for the EconCS complexity interfaces

This module contains certificate constructors, equivalence theorems, and proof
combinators for the semantic declarations in `Complexity.Definitions.Interfaces`.
-/

namespace EconCSLib
namespace OpenProblem
namespace EconCSBench

universe u v w

open Filter Asymptotics

/-! ## Natural-valued polynomial certificates -/

/-- The open-ended certificate interface and `PolynomialCostBound` express
exactly the same mathematical property. -/
theorem nonempty_polynomialCostCertificate_iff
    {Input : Type u} (sizeOf : Input → ℕ) (cost : Input → ℕ) :
    Nonempty (PolynomialCostCertificate sizeOf cost) ↔
      PolynomialCostBound sizeOf cost :=
  UnitCostRAM.IsPolyBound.nonempty_polynomialMajorantCertificate_iff

/-- Characterization using Mathlib's standard polynomial datatype. -/
theorem polynomialCostBound_iff_exists_polynomial
    {Input : Type u} (sizeOf : Input → ℕ) (cost : Input → ℕ) :
    PolynomialCostBound sizeOf cost ↔
      ∃ polynomial : Polynomial ℕ, ∀ input,
        cost input ≤ polynomial.eval (sizeOf input) :=
  UnitCostRAM.IsPolyBound.iff_exists_natPolynomial

theorem nonempty_multivariatePolynomialCostCertificate_iff
    {Input : Type u} {Parameter : Type v}
    (sizes : Input → Parameter → ℕ) (cost : Input → ℕ) :
    Nonempty (MultivariatePolynomialCostCertificate sizes cost) ↔
      MultivariatePolynomialCostBound sizes cost :=
  UnitCostRAM.nonempty_mvPolynomialMajorantCertificate_iff

/-- Named-parameter and aggregate-size definitions agree for every fixed
finite parameter family. -/
theorem multivariatePolynomialCostBound_iff_aggregate
    {Input : Type u} {Parameter : Type v} [Fintype Parameter]
    (sizes : Input → Parameter → ℕ) (cost : Input → ℕ) :
    MultivariatePolynomialCostBound sizes cost ↔
      PolynomialCostBound
        (fun input ↦ ∑ parameter, sizes input parameter) cost :=
  UnitCostRAM.isMvPolynomialBound_iff_aggregate sizes cost

/-! ## Expected-cost certificates -/

namespace PolynomialExpectedCostCertificate

/-- Every nonnegative uniformly bounded real formula has a constant
polynomial certificate. -/
noncomputable def ofBounded
    {Input : Type u} {sizeOf : Input → ℕ} {cost : Input → ℝ}
    (upper : ℕ) (nonnegative : ∀ input, 0 ≤ cost input)
    (bound : ∀ input, cost input ≤ (upper : ℝ)) :
    PolynomialExpectedCostCertificate sizeOf cost :=
  ⟨Polynomial.C upper, nonnegative, fun input ↦ by
    simpa using bound input⟩

/-- Certify a real-valued formula by bounding it with a certified natural
counter. -/
noncomputable def ofNatUpperBound
    {Input : Type u} {sizeOf : Input → ℕ}
    {cost : Input → ℝ} {upper : Input → ℕ}
    (upperCertificate : PolynomialCostCertificate sizeOf upper)
    (nonnegative : ∀ input, 0 ≤ cost input)
    (bound : ∀ input, cost input ≤ (upper input : ℝ)) :
    PolynomialExpectedCostCertificate sizeOf cost :=
  ⟨upperCertificate.polynomial, nonnegative, fun input ↦
    (bound input).trans (by exact_mod_cast upperCertificate.bound input)⟩

/-- Replace a certified real formula by any nonnegative pointwise smaller
formula. -/
def ofLE
    {Input : Type u} {sizeOf : Input → ℕ} {left right : Input → ℝ}
    (rightCertificate : PolynomialExpectedCostCertificate sizeOf right)
    (nonnegative : ∀ input, 0 ≤ left input)
    (bound : ∀ input, left input ≤ right input) :
    PolynomialExpectedCostCertificate sizeOf left :=
  ⟨rightCertificate.polynomial, nonnegative, fun input ↦
    (bound input).trans (rightCertificate.bound input)⟩

/-- Real polynomial-majorant certificates compose under addition. -/
noncomputable def add
    {Input : Type u} {sizeOf : Input → ℕ} {left right : Input → ℝ}
    (leftCertificate : PolynomialExpectedCostCertificate sizeOf left)
    (rightCertificate : PolynomialExpectedCostCertificate sizeOf right) :
    PolynomialExpectedCostCertificate sizeOf
      (fun input ↦ left input + right input) :=
  ⟨leftCertificate.polynomial + rightCertificate.polynomial,
    fun input ↦ add_nonneg (leftCertificate.nonnegative input)
      (rightCertificate.nonnegative input),
    fun input ↦ by
      simpa only [Polynomial.eval_add, Nat.cast_add] using
        add_le_add (leftCertificate.bound input)
          (rightCertificate.bound input)⟩

/-- Real polynomial-majorant certificates compose under multiplication. -/
noncomputable def mul
    {Input : Type u} {sizeOf : Input → ℕ} {left right : Input → ℝ}
    (leftCertificate : PolynomialExpectedCostCertificate sizeOf left)
    (rightCertificate : PolynomialExpectedCostCertificate sizeOf right) :
    PolynomialExpectedCostCertificate sizeOf
      (fun input ↦ left input * right input) :=
  ⟨leftCertificate.polynomial * rightCertificate.polynomial,
    fun input ↦ mul_nonneg (leftCertificate.nonnegative input)
      (rightCertificate.nonnegative input),
    fun input ↦ by
      rw [Polynomial.eval_mul, Nat.cast_mul]
      exact mul_le_mul (leftCertificate.bound input)
        (rightCertificate.bound input)
        (rightCertificate.nonnegative input)
        (by positivity)⟩

/-- Real polynomial-majorant certificates compose under a fixed natural
power. -/
noncomputable def pow
    {Input : Type u} {sizeOf : Input → ℕ} {cost : Input → ℝ}
    (certificate : PolynomialExpectedCostCertificate sizeOf cost)
    (exponent : ℕ) :
    PolynomialExpectedCostCertificate sizeOf
      (fun input ↦ cost input ^ exponent) :=
  ⟨certificate.polynomial ^ exponent,
    fun input ↦ pow_nonneg (certificate.nonnegative input) exponent,
    fun input ↦ by
      rw [Polynomial.eval_pow, Nat.cast_pow]
      exact pow_le_pow_left₀ (certificate.nonnegative input)
        (certificate.bound input) exponent⟩

end PolynomialExpectedCostCertificate

/-- The real-valued certificate is equivalent to the expected-cost
predicate. -/
theorem nonempty_polynomialExpectedCostCertificate_iff
    {Input : Type u} (sizeOf : Input → ℕ) (cost : Input → ℝ) :
    Nonempty (PolynomialExpectedCostCertificate sizeOf cost) ↔
      PolynomialExpectedCostBound sizeOf cost := by
  constructor
  · rintro ⟨certificate⟩
    refine ⟨certificate.nonnegative, ?_⟩
    obtain ⟨coefficient, exponent, polynomialBound⟩ :=
      UnitCostRAM.IsPolyBound.natPolynomialEval_comp
        (sizeOf := sizeOf) certificate.polynomial
    refine ⟨coefficient, exponent, fun input ↦
      (certificate.bound input).trans ?_⟩
    exact_mod_cast polynomialBound input
  · rintro ⟨nonnegative, coefficient, exponent, bound⟩
    let polynomial : Polynomial ℕ :=
      Polynomial.C coefficient * (Polynomial.X + 1) ^ exponent
    refine ⟨⟨polynomial, nonnegative, fun input ↦ ?_⟩⟩
    simpa [polynomial, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow] using bound input

/-- A global pointwise certificate implies Mathlib's asymptotic
formulation. -/
theorem PolynomialExpectedCostCertificate.isRealAsymptoticallyPolynomial
    {cost : ℕ → ℝ}
    (certificate : PolynomialExpectedCostCertificate id cost) :
    IsRealAsymptoticallyPolynomial cost := by
  have semantic : PolynomialExpectedCostBound id cost :=
    nonempty_polynomialExpectedCostCertificate_iff id cost |>.mp
      ⟨certificate⟩
  obtain ⟨nonnegative, coefficient, exponent, bound⟩ := semantic
  refine ⟨exponent, isBigO_iff.mpr ⟨(coefficient : ℝ), ?_⟩⟩
  filter_upwards [] with n
  simp only [Real.norm_eq_abs, abs_pow]
  rw [abs_of_nonneg (nonnegative n), abs_of_nonneg (by positivity)]
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    bound n

/-- Pointwise expected-cost polynomiality agrees with the standard
asymptotic formulation on natural input sizes. -/
theorem polynomialExpectedCostBound_iff_isRealAsymptoticallyPolynomial
    (cost : ℕ → ℝ) :
    PolynomialExpectedCostBound id cost ↔
      (∀ n, 0 ≤ cost n) ∧ IsRealAsymptoticallyPolynomial cost := by
  constructor
  · intro bound
    obtain ⟨nonnegative, coefficient, exponent, pointwise⟩ := bound
    refine ⟨nonnegative, exponent, isBigO_iff.mpr ⟨(coefficient : ℝ), ?_⟩⟩
    filter_upwards [] with n
    simp only [Real.norm_eq_abs, abs_pow]
    rw [abs_of_nonneg (nonnegative n), abs_of_nonneg (by positivity)]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      pointwise n
  · rintro ⟨nonnegative, exponent, asymptotic⟩
    obtain ⟨constant, constantPositive, globalBound⟩ :=
      bound_of_isBigO_nat_atTop asymptotic
    obtain ⟨coefficient, coefficientBound⟩ := exists_nat_ge constant
    refine ⟨nonnegative, coefficient, exponent, fun n ↦ ?_⟩
    have comparison := globalBound (x := n) (by positivity :
      (((n + 1 : ℕ) : ℝ) ^ exponent) ≠ 0)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (nonnegative n), abs_of_nonneg (by positivity)] at comparison
    exact comparison.trans <| calc
      constant * (((n + 1 : ℕ) : ℝ) ^ exponent) ≤
          (coefficient : ℝ) * (((n + 1 : ℕ) : ℝ) ^ exponent) :=
        mul_le_mul_of_nonneg_right coefficientBound (by positivity)
      _ = ((coefficient * (n + 1) ^ exponent : ℕ) : ℝ) := by
        norm_num

theorem nonempty_multivariatePolynomialExpectedCostCertificate_iff
    {Input : Type u} {Parameter : Type v}
    (sizes : Input → Parameter → ℕ) (cost : Input → ℝ) :
    Nonempty (MultivariatePolynomialExpectedCostCertificate sizes cost) ↔
      MultivariatePolynomialExpectedCostBound sizes cost := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.nonnegative, certificate.polynomial, certificate.bound⟩
  · rintro ⟨nonnegative, polynomial, bound⟩
    exact ⟨⟨polynomial, nonnegative, bound⟩⟩

/-! ## Potential-method amortized analysis -/

/-- Telescoping theorem for the potential method. -/
theorem AmortizedCertificate.sequence_bound
    {State : Type u} {Operation : Type v}
    {next : State → Operation → State}
    {actualCost : State → Operation → ℕ}
    {chargedCost : Operation → ℕ}
    (certificate :
      AmortizedCertificate State Operation next actualCost chargedCost)
    (operations : List Operation) (initial : State) :
    operationSequenceCost next actualCost operations initial +
        certificate.potential
          (runOperationSequence next operations initial) ≤
      (operations.map chargedCost).sum + certificate.potential initial := by
  induction operations generalizing initial with
  | nil => simp [operationSequenceCost, runOperationSequence]
  | cons operation operations ih =>
      simp only [operationSequenceCost, runOperationSequence, List.map_cons,
        List.sum_cons]
      have hstep := certificate.step_bound initial operation
      have htail := ih (next initial operation)
      omega

/-- Total actual cost is at most total charged cost plus initial potential. -/
theorem AmortizedCertificate.total_actual_le
    {State : Type u} {Operation : Type v}
    {next : State → Operation → State}
    {actualCost : State → Operation → ℕ}
    {chargedCost : Operation → ℕ}
    (certificate :
      AmortizedCertificate State Operation next actualCost chargedCost)
    (operations : List Operation) (initial : State) :
    operationSequenceCost next actualCost operations initial ≤
      (operations.map chargedCost).sum + certificate.potential initial := by
  exact (Nat.le_add_right _ _).trans
    (certificate.sequence_bound operations initial)

/-! ## Canonical-output strict reductions -/

namespace FixedEncodingPolynomialSearchReduction

/-- The first stage emits exactly the target problem's canonical input words. -/
theorem inputProgram_outputs_canonical
    {source target : SearchProblem}
    {sourceInputEncoding : UnitCostRAM.Encoding source.Input}
    {sourceOutputEncoding : UnitCostRAM.DependentEncoding source.Output}
    {targetInputEncoding : UnitCostRAM.Encoding target.Input}
    {targetOutputEncoding : UnitCostRAM.DependentEncoding target.Output}
    (reduction : FixedEncodingPolynomialSearchReduction source target
      sourceInputEncoding sourceOutputEncoding
      targetInputEncoding targetOutputEncoding)
    (input : source.Input) :
    ∃ finalState,
      (UnitCostRAM.run
          (UnitCostRAM.closedEnvironment fun _ => false)
          reduction.inputProgram.program
          (reduction.inputProgram.fuel input)
          (sourceInputEncoding.encode input)).ret =
        .halted (targetInputEncoding.encode (reduction.mapInput input))
          finalState := by
  simpa [UnitCostRAM.Encoding.dependent] using
    reduction.inputProgram.correct input

/-- The decoding stage emits exactly the canonical source-solution encoding. -/
theorem outputProgram_outputs_canonical
    {source target : SearchProblem}
    {sourceInputEncoding : UnitCostRAM.Encoding source.Input}
    {sourceOutputEncoding : UnitCostRAM.DependentEncoding source.Output}
    {targetInputEncoding : UnitCostRAM.Encoding target.Input}
    {targetOutputEncoding : UnitCostRAM.DependentEncoding target.Output}
    (reduction : FixedEncodingPolynomialSearchReduction source target
      sourceInputEncoding sourceOutputEncoding
      targetInputEncoding targetOutputEncoding)
    (pair : Σ input, target.Output (reduction.mapInput input)) :
    ∃ finalState,
      (UnitCostRAM.run
          (UnitCostRAM.closedEnvironment fun _ => false)
          reduction.outputProgram.program
          (reduction.outputProgram.fuel pair)
          ((UnitCostRAM.Encoding.sigma sourceInputEncoding
            (targetOutputEncoding.comap reduction.mapInput)).encode pair)).ret =
        .halted
          (sourceOutputEncoding.encode pair.1
            (reduction.mapOutput pair.1 pair.2))
          finalState := by
  simpa [UnitCostRAM.DependentEncoding.comap] using
    reduction.outputProgram.correct pair

end FixedEncodingPolynomialSearchReduction

end EconCSBench
end OpenProblem
end EconCSLib
