/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.UnitCostRAM
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Log

/-!
# Polynomial size growth for unit-cost RAM computations

Polynomial running-time proofs are not closed under sequential composition
from time bounds alone: the input presented to the second computation is an
output of the first computation, so its representation size must also be
controlled.  Similarly, a loop body whose cost depends on the current state
needs a polynomial bound on every state that is actually reached.

This module supplies those missing certificates without changing the
unit-cost RAM model into a bit-level Turing machine.  It follows the useful
proof architecture of `Turing.TM2ComputableInPolyTime` and its composition and
bounded-fold developments in OpenAI's `ten-proofs/GapCVP.lean`:

* mathematical functions remain linked to concrete costed implementations;
* output and intermediate-state sizes have explicit polynomial majorants;
* sequential composition substitutes a polynomial output-size bound into the
  cost bound of the continuation;
* counted and fuelled loops need bounds only on reachable states.

The semantic endpoint reuses Mathlib's `Polynomial ℕ` and
`MvPolynomial Parameter ℕ`.  The former is proved equivalent to the
coefficient/exponent normal form used by the lightweight checker.  The latter
provides genuine named multivariate bounds, with a theorem showing that for a
fixed finite parameter family this is equivalent to a polynomial in the sum
of the parameters.

The size functions are deliberately abstract.  For representation-aware
claims, instantiate them with `Encoding.size` or `DependentEncoding.size`.
For an exact-real RAM, each real occupies one word, consistently with
`UnitCostRAM.Word.real`; this module never replaces reals by bit strings.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM

universe u v w x

/-! ## Equivalence with polynomial witnesses from Mathlib -/

namespace IsPolyBound

variable {Input : Type u} {sizeOf : Input → ℕ}

/-- A fixed natural power of a polynomially bounded function remains
polynomially bounded. -/
theorem pow {cost : Input → ℕ} (hcost : IsPolyBound sizeOf cost)
    (exponent : ℕ) :
    IsPolyBound sizeOf (fun input ↦ (cost input) ^ exponent) := by
  induction exponent with
  | zero =>
      simpa using (IsPolyBound.const (sizeOf := sizeOf) 1)
  | succ exponent ih =>
      simpa [pow_succ] using IsPolyBound.mul ih hcost

/-- Evaluation of a polynomial with natural coefficients is polynomially
bounded in its argument.  This is the representation of a time bound used by
Mathlib's `Turing.TM2ComputableInPolyTime`. -/
theorem natPolynomialEval (polynomial : Polynomial ℕ) :
    IsPolyBound id polynomial.eval := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      simpa [Polynomial.eval_add] using IsPolyBound.add leftIH rightIH
  | monomial exponent coefficient =>
      simpa [Polynomial.eval_monomial] using
        IsPolyBound.mul
          (IsPolyBound.const (sizeOf := id) coefficient)
          (IsPolyBound.pow (IsPolyBound.self (sizeOf := id)) exponent)

/-- Substituting the selected input-size measure into a natural polynomial
produces a polynomially bounded function on arbitrary inputs. -/
theorem natPolynomialEval_comp (polynomial : Polynomial ℕ) :
    IsPolyBound sizeOf (fun input ↦ polynomial.eval (sizeOf input)) := by
  obtain ⟨coefficient, exponent, bound⟩ := natPolynomialEval polynomial
  exact ⟨coefficient, exponent, fun input ↦ bound (sizeOf input)⟩

/-- The monomial-majorant definition used by `UnitCostRAM.IsPolyBound` is
equivalent to existence of an arbitrary natural-coefficient polynomial
majorant, as used by the Turing-machine interface in Mathlib. -/
theorem iff_exists_natPolynomial {cost : Input → ℕ} :
    IsPolyBound sizeOf cost ↔
      ∃ polynomial : Polynomial ℕ, ∀ input,
        cost input ≤ polynomial.eval (sizeOf input) := by
  constructor
  · rintro ⟨coefficient, exponent, bound⟩
    refine ⟨Polynomial.C coefficient * (Polynomial.X + 1) ^ exponent, ?_⟩
    intro input
    simpa [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] using bound input
  · rintro ⟨polynomial, bound⟩
    exact IsPolyBound.of_le (natPolynomialEval_comp polynomial) bound

/-! ## Closure rules for common algorithmic bounds -/

/-- Taking a pointwise maximum preserves polynomial boundedness.  This is the
basic rule used for worst-case branches. -/
theorem maximum {left right : Input → ℕ}
    (hleft : IsPolyBound sizeOf left)
    (hright : IsPolyBound sizeOf right) :
    IsPolyBound sizeOf (fun input ↦ max (left input) (right input)) := by
  apply IsPolyBound.of_le (IsPolyBound.add hleft hright)
  intro input
  omega

/-- Taking a pointwise minimum preserves polynomial boundedness. -/
theorem minimum_left {left right : Input → ℕ}
    (hleft : IsPolyBound sizeOf left) :
    IsPolyBound sizeOf (fun input ↦ min (left input) (right input)) :=
  IsPolyBound.of_le hleft fun input ↦
    min_le_left (left input) (right input)

/-- Truncated subtraction cannot increase the left-hand cost. -/
theorem tsub {left right : Input → ℕ}
    (hleft : IsPolyBound sizeOf left) :
    IsPolyBound sizeOf (fun input ↦ left input - right input) :=
  IsPolyBound.of_le hleft fun input ↦
    Nat.sub_le (left input) (right input)

/-- A natural logarithm of a polynomially bounded quantity is polynomially
bounded.  This intentionally gives a conservative polynomial certificate;
it does not attempt to preserve a logarithmic complexity class. -/
theorem logarithm (base : ℕ) {argument : Input → ℕ}
    (hargument : IsPolyBound sizeOf argument) :
    IsPolyBound sizeOf (fun input ↦ Nat.log base (argument input)) :=
  IsPolyBound.of_le hargument fun input ↦
    Nat.log_le_self base (argument input)

/-- Select one of two polynomial bounds using an arbitrary predicate. -/
theorem ite (condition : Input → Prop) [DecidablePred condition]
    {ifTrue ifFalse : Input → ℕ}
    (htrue : IsPolyBound sizeOf ifTrue)
    (hfalse : IsPolyBound sizeOf ifFalse) :
    IsPolyBound sizeOf
      (fun input ↦ if condition input then ifTrue input else ifFalse input) := by
  apply IsPolyBound.of_le (IsPolyBound.maximum htrue hfalse)
  intro input
  split <;> simp_all

/-- A sum over a fixed finite index set preserves polynomial boundedness.
The individual hidden constants may depend on the index because the index set
itself is fixed and finite. -/
theorem finset_sum {Index : Type v} (indices : Finset Index)
    (cost : Index → Input → ℕ)
    (hcost : ∀ index ∈ indices, IsPolyBound sizeOf (cost index)) :
    IsPolyBound sizeOf (fun input ↦ ∑ index ∈ indices, cost index input) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using IsPolyBound.const (sizeOf := sizeOf) 0
  | @insert index indices notMem ih =>
      have hindex := hcost index (Finset.mem_insert_self index indices)
      have hrest : ∀ item ∈ indices, IsPolyBound sizeOf (cost item) :=
        fun item membership ↦ hcost item (Finset.mem_insert_of_mem membership)
      simpa [Finset.sum_insert, notMem] using IsPolyBound.add hindex (ih hrest)

/-- Substitute a polynomially bounded intermediate natural value into a
polynomially bounded outer cost.  This is the scalar core of sequential
composition; representation-aware algorithms additionally need a checked
output-size certificate. -/
theorem comp {inner : Input → ℕ} {outer : ℕ → ℕ}
    (hinner : IsPolyBound sizeOf inner)
    (houter : IsPolyBound id outer) :
    IsPolyBound sizeOf (fun input ↦ outer (inner input)) := by
  obtain ⟨coefficient, exponent, outerBound⟩ := houter
  apply IsPolyBound.of_le
    (IsPolyBound.mul
      (IsPolyBound.const (sizeOf := sizeOf) coefficient)
      (IsPolyBound.pow
        (IsPolyBound.add hinner (IsPolyBound.const 1)) exponent))
  intro input
  exact outerBound (inner input)

/-- A product over a fixed finite index set preserves polynomial
boundedness.  The finiteness must be independent of the input; a
polynomially-growing number of nonconstant factors may be exponential. -/
theorem finset_prod {Index : Type v} (indices : Finset Index)
    (cost : Index → Input → ℕ)
    (hcost : ∀ index ∈ indices, IsPolyBound sizeOf (cost index)) :
    IsPolyBound sizeOf (fun input ↦ ∏ index ∈ indices, cost index input) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using IsPolyBound.const (sizeOf := sizeOf) 1
  | @insert index indices notMem ih =>
      have hindex := hcost index (Finset.mem_insert_self index indices)
      have hrest : ∀ item ∈ indices, IsPolyBound sizeOf (cost item) :=
        fun item membership ↦ hcost item (Finset.mem_insert_of_mem membership)
      simpa [Finset.prod_insert, notMem] using IsPolyBound.mul hindex (ih hrest)

end IsPolyBound

/-! ## Genuine multivariate polynomial bounds -/

/-- A resource counter is bounded by one multivariate polynomial with natural
coefficients in a family of named size parameters.

Unlike the list interface `IsPolyBoundInSizes`, this definition retains the
identity of every parameter.  The variable type need not be finite: every
`MvPolynomial` mentions only finitely many variables.  For a fixed finite
parameter type the definition is equivalent to a univariate polynomial bound
in the sum of all parameters; see `isMvPolynomialBound_iff_aggregate` below. -/
def IsMvPolynomialBound {Input : Type u} {Parameter : Type v}
    (sizes : Input → Parameter → ℕ) (cost : Input → ℕ) : Prop :=
  ∃ polynomial : MvPolynomial Parameter ℕ, ∀ input,
    cost input ≤ polynomial.eval (sizes input)

/-- Promise-problem version of `IsMvPolynomialBound`. -/
def IsMvPolynomialBoundOn {Input : Type u} {Parameter : Type v}
    (valid : Input → Prop) (sizes : Input → Parameter → ℕ)
    (cost : Input → ℕ) : Prop :=
  ∃ polynomial : MvPolynomial Parameter ℕ, ∀ input, valid input →
    cost input ≤ polynomial.eval (sizes input)

/-- One multivariate polynomial uniformly bounds every randomized, oracle,
adversarial, or nondeterministic execution choice.  Neither its coefficients
nor its support may depend on the choice. -/
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

namespace IsMvPolynomialBound

variable {Input : Type u} {Parameter : Type v}
  {sizes : Input → Parameter → ℕ}

theorem const (value : ℕ) :
    IsMvPolynomialBound sizes (fun _ ↦ value) :=
  ⟨MvPolynomial.C value, fun _ ↦ by simp⟩

theorem coordinate (parameter : Parameter) :
    IsMvPolynomialBound sizes (fun input ↦ sizes input parameter) :=
  ⟨MvPolynomial.X parameter, fun _ ↦ by simp⟩

theorem of_le {left right : Input → ℕ}
    (hright : IsMvPolynomialBound sizes right)
    (hle : ∀ input, left input ≤ right input) :
    IsMvPolynomialBound sizes left := by
  obtain ⟨polynomial, bound⟩ := hright
  exact ⟨polynomial, fun input ↦ (hle input).trans (bound input)⟩

theorem add {left right : Input → ℕ}
    (hleft : IsMvPolynomialBound sizes left)
    (hright : IsMvPolynomialBound sizes right) :
    IsMvPolynomialBound sizes (fun input ↦ left input + right input) := by
  obtain ⟨leftPolynomial, leftBound⟩ := hleft
  obtain ⟨rightPolynomial, rightBound⟩ := hright
  refine ⟨leftPolynomial + rightPolynomial, fun input ↦ ?_⟩
  rw [MvPolynomial.eval_add]
  exact Nat.add_le_add (leftBound input) (rightBound input)

theorem mul {left right : Input → ℕ}
    (hleft : IsMvPolynomialBound sizes left)
    (hright : IsMvPolynomialBound sizes right) :
    IsMvPolynomialBound sizes (fun input ↦ left input * right input) := by
  obtain ⟨leftPolynomial, leftBound⟩ := hleft
  obtain ⟨rightPolynomial, rightBound⟩ := hright
  refine ⟨leftPolynomial * rightPolynomial, fun input ↦ ?_⟩
  rw [MvPolynomial.eval_mul]
  exact Nat.mul_le_mul (leftBound input) (rightBound input)

theorem pow {cost : Input → ℕ}
    (hcost : IsMvPolynomialBound sizes cost) (exponent : ℕ) :
    IsMvPolynomialBound sizes (fun input ↦ cost input ^ exponent) := by
  obtain ⟨polynomial, bound⟩ := hcost
  refine ⟨polynomial ^ exponent, fun input ↦ ?_⟩
  rw [MvPolynomial.eval_pow]
  exact Nat.pow_le_pow_left (bound input) exponent

theorem maximum {left right : Input → ℕ}
    (hleft : IsMvPolynomialBound sizes left)
    (hright : IsMvPolynomialBound sizes right) :
    IsMvPolynomialBound sizes (fun input ↦ max (left input) (right input)) := by
  apply IsMvPolynomialBound.of_le (IsMvPolynomialBound.add hleft hright)
  intro input
  omega

end IsMvPolynomialBound

/-- Every natural-coefficient multivariate polynomial evaluated on a fixed
finite vector is polynomially bounded in the sum of that vector. -/
theorem isPolyBound_mvPolynomialEval_aggregate
    {Input : Type u} {Parameter : Type v} [Fintype Parameter]
    (sizes : Input → Parameter → ℕ)
    (polynomial : MvPolynomial Parameter ℕ) :
    IsPolyBound (fun input ↦ ∑ parameter, sizes input parameter)
      (fun input ↦ polynomial.eval (sizes input)) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C value =>
      simpa using IsPolyBound.const
        (sizeOf := fun input ↦ ∑ parameter, sizes input parameter) value
  | add left right leftIH rightIH =>
      simpa [MvPolynomial.eval_add] using IsPolyBound.add leftIH rightIH
  | mul_X polynomial parameter polynomialIH =>
      have coordinateBound :
          IsPolyBound (fun input ↦ ∑ parameter, sizes input parameter)
            (fun input ↦ sizes input parameter) := by
        apply IsPolyBound.of_le IsPolyBound.self
        intro input
        exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ parameter)
      simpa [MvPolynomial.eval_mul] using
        IsPolyBound.mul polynomialIH coordinateBound

/-- For a fixed finite family of named parameters, a genuine multivariate
polynomial bound is equivalent to the usual complexity-theory convention of
one polynomial in their aggregate size. -/
theorem isMvPolynomialBound_iff_aggregate
    {Input : Type u} {Parameter : Type v} [Fintype Parameter]
    (sizes : Input → Parameter → ℕ) (cost : Input → ℕ) :
    IsMvPolynomialBound sizes cost ↔
      IsPolyBound (fun input ↦ ∑ parameter, sizes input parameter) cost := by
  classical
  constructor
  · rintro ⟨polynomial, bound⟩
    exact IsPolyBound.of_le
      (isPolyBound_mvPolynomialEval_aggregate sizes polynomial) bound
  · rintro ⟨coefficient, exponent, bound⟩
    let aggregatePolynomial : MvPolynomial Parameter ℕ :=
      ∑ parameter : Parameter, MvPolynomial.X parameter
    refine ⟨MvPolynomial.C coefficient *
      (aggregatePolynomial + MvPolynomial.C 1) ^ exponent, fun input ↦ ?_⟩
    simpa [aggregatePolynomial, MvPolynomial.eval_mul,
      MvPolynomial.eval_add, MvPolynomial.eval_pow,
      MvPolynomial.eval_sum] using bound input

/-- Choice-uniform counterpart of `isMvPolynomialBound_iff_aggregate`. -/
theorem isUniformMvPolynomialBound_iff_aggregate
    {Input : Type u} {Parameter : Type v} {Choice : Input → Type w}
    [Fintype Parameter]
    (sizes : Input → Parameter → ℕ)
    (cost : (input : Input) → Choice input → ℕ) :
    IsUniformMvPolynomialBound sizes cost ↔
      IsUniformPolyBound
        (fun input ↦ ∑ parameter, sizes input parameter) cost := by
  classical
  constructor
  · rintro ⟨polynomial, bound⟩
    obtain ⟨coefficient, exponent, polynomialBound⟩ :=
      isPolyBound_mvPolynomialEval_aggregate sizes polynomial
    exact ⟨coefficient, exponent, fun input choice ↦
      (bound input choice).trans (polynomialBound input)⟩
  · rintro ⟨coefficient, exponent, bound⟩
    let aggregatePolynomial : MvPolynomial Parameter ℕ :=
      ∑ parameter : Parameter, MvPolynomial.X parameter
    refine ⟨MvPolynomial.C coefficient *
      (aggregatePolynomial + MvPolynomial.C 1) ^ exponent,
      fun input choice ↦ ?_⟩
    simpa [aggregatePolynomial, MvPolynomial.eval_mul,
      MvPolynomial.eval_add, MvPolynomial.eval_pow,
      MvPolynomial.eval_sum] using bound input choice

/-! ## Polynomial output-size certificates -/

/-- A checked upper bound for the size of the output of a dependent
mathematical function.  Keeping `bound` as data makes the certificate usable
when the function is fed to a later computation. -/
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

/-- Direct characterization of polynomial output size without exposing the
chosen majorant. -/
theorem hasPolynomialOutputSize_iff
    {Input : Type u} {Output : Input → Type v}
    {sizeOf : Input → ℕ}
    {outputSize : (input : Input) → Output input → ℕ}
    {function : (input : Input) → Output input} :
    HasPolynomialOutputSize sizeOf outputSize function ↔
      IsPolyBound sizeOf (fun input ↦ outputSize input (function input)) := by
  constructor
  · rintro ⟨certificate, polynomial⟩
    exact IsPolyBound.of_le polynomial certificate.output_le
  · intro polynomial
    exact ⟨⟨_, fun _ ↦ le_rfl⟩, polynomial⟩

/-- Representation-aware specialization using a lossless dependent output
encoding. -/
def HasPolynomialEncodedOutputSize
    {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ) (encoding : DependentEncoding Output)
    (function : (input : Input) → Output input) : Prop :=
  HasPolynomialOutputSize sizeOf encoding.size function

/-- Checked output-size majorant uniform over a random seed, legal oracle,
tie-breaking rule, or other execution choice.  The bound may depend on the
ordinary input but not on the auxiliary choice. -/
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

/-- Uniform polynomial output size for computations with auxiliary choices.
One polynomial must work for every legal choice. -/
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

theorem hasUniformPolynomialOutputSize_iff
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {sizeOf : Input → ℕ}
    {outputSize : (input : Input) → (choice : Choice input) →
      Output input choice → ℕ}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice} :
    HasUniformPolynomialOutputSize sizeOf outputSize function ↔
      IsUniformPolyBound sizeOf
        (fun input choice ↦ outputSize input choice
          (function input choice)) := by
  constructor
  · rintro ⟨certificate, coefficient, exponent, polynomial⟩
    exact ⟨coefficient, exponent, fun input choice ↦
      (certificate.output_le input choice).trans (polynomial input)⟩
  · rintro ⟨coefficient, exponent, polynomial⟩
    refine ⟨⟨fun input ↦ coefficient * (sizeOf input + 1) ^ exponent,
      polynomial⟩, coefficient, exponent, ?_⟩
    exact fun _ ↦ le_rfl

namespace IsUniformPolyBound

variable {Input : Type u} {Choice : Input → Type v}
  {sizeOf : Input → ℕ}

theorem of_le {left right : (input : Input) → Choice input → ℕ}
    (hright : IsUniformPolyBound sizeOf right)
    (hle : ∀ input choice, left input choice ≤ right input choice) :
    IsUniformPolyBound sizeOf left := by
  obtain ⟨coefficient, exponent, bound⟩ := hright
  exact ⟨coefficient, exponent, fun input choice ↦
    (hle input choice).trans (bound input choice)⟩

theorem add {left right : (input : Input) → Choice input → ℕ}
    (hleft : IsUniformPolyBound sizeOf left)
    (hright : IsUniformPolyBound sizeOf right) :
    IsUniformPolyBound sizeOf
      (fun input choice ↦ left input choice + right input choice) := by
  obtain ⟨leftCoefficient, leftExponent, hleft⟩ := hleft
  obtain ⟨rightCoefficient, rightExponent, hright⟩ := hright
  refine ⟨leftCoefficient + rightCoefficient,
    max leftExponent rightExponent, ?_⟩
  intro input choice
  have hbase : 1 ≤ sizeOf input + 1 := by omega
  have hpowLeft :
      (sizeOf input + 1) ^ leftExponent ≤
        (sizeOf input + 1) ^ max leftExponent rightExponent :=
    Nat.pow_le_pow_right hbase (le_max_left _ _)
  have hpowRight :
      (sizeOf input + 1) ^ rightExponent ≤
        (sizeOf input + 1) ^ max leftExponent rightExponent :=
    Nat.pow_le_pow_right hbase (le_max_right _ _)
  calc
    left input choice + right input choice
        ≤ leftCoefficient * (sizeOf input + 1) ^ leftExponent +
          rightCoefficient * (sizeOf input + 1) ^ rightExponent :=
      Nat.add_le_add (hleft input choice) (hright input choice)
    _ ≤ leftCoefficient *
            (sizeOf input + 1) ^ max leftExponent rightExponent +
          rightCoefficient *
            (sizeOf input + 1) ^ max leftExponent rightExponent := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left leftCoefficient hpowLeft)
        (Nat.mul_le_mul_left rightCoefficient hpowRight)
    _ = (leftCoefficient + rightCoefficient) *
          (sizeOf input + 1) ^ max leftExponent rightExponent := by ring

end IsUniformPolyBound

/-! ## Cost bounds relative to an intermediate value -/

/-- A cost is polynomial uniformly in the original input size and in the
size of a dependent intermediate value.  Uniformity over `value` prevents a
continuation from choosing different hidden polynomial constants for
different intermediate results. -/
def IsPolyBoundInInputAndValueSize
    {Input : Type u} {Value : Input → Type v}
    (inputSize : Input → ℕ)
    (valueSize : (input : Input) → Value input → ℕ)
    (cost : (input : Input) → Value input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ, ∀ input value,
    cost input value ≤
      coefficient *
        (inputSize input + valueSize input value + 1) ^ exponent

/-- Choice-uniform counterpart of `IsPolyBoundInInputAndValueSize`.  The
hidden polynomial cannot depend on the random seed, oracle, or tie-breaking
rule. -/
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

namespace IsPolyBoundInInputAndValueSize

/-- Substitution principle: if the selected intermediate values have
polynomial size, a uniform polynomial bound in input-and-value size becomes
a polynomial bound in the original input size alone. -/
theorem specialize
    {Input : Type u} {Value : Input → Type v}
    {inputSize : Input → ℕ}
    {valueSize : (input : Input) → Value input → ℕ}
    {cost : (input : Input) → Value input → ℕ}
    (hcost : IsPolyBoundInInputAndValueSize inputSize valueSize cost)
    (value : (input : Input) → Value input)
    (hvalue : IsPolyBound inputSize
      (fun input ↦ valueSize input (value input))) :
    IsPolyBound inputSize (fun input ↦ cost input (value input)) := by
  obtain ⟨coefficient, exponent, hcost⟩ := hcost
  have hbase : IsPolyBound inputSize (fun input ↦
      inputSize input + valueSize input (value input) + 1) :=
    IsPolyBound.add
      (IsPolyBound.add (IsPolyBound.self (sizeOf := inputSize)) hvalue)
      (IsPolyBound.const 1)
  have hmajorant : IsPolyBound inputSize (fun input ↦
      coefficient *
        (inputSize input + valueSize input (value input) + 1) ^ exponent) :=
    IsPolyBound.mul (IsPolyBound.const coefficient)
      (IsPolyBound.pow hbase exponent)
  exact IsPolyBound.of_le hmajorant fun input ↦ hcost input (value input)

end IsPolyBoundInInputAndValueSize

namespace IsUniformPolyBoundInInputAndValueSize

/-- Substitute a uniformly polynomial-sized choice-dependent intermediate
value into a local input-and-value cost polynomial. -/
theorem specialize
    {Input : Type u} {Choice : Input → Type v}
    {Value : (input : Input) → Choice input → Type w}
    {inputSize : Input → ℕ}
    {valueSize : (input : Input) → (choice : Choice input) →
      Value input choice → ℕ}
    {cost : (input : Input) → (choice : Choice input) →
      Value input choice → ℕ}
    (hcost : IsUniformPolyBoundInInputAndValueSize
      inputSize valueSize cost)
    (value : (input : Input) → (choice : Choice input) →
      Value input choice)
    (hvalue : IsUniformPolyBound inputSize
      (fun input choice ↦ valueSize input choice (value input choice))) :
    IsUniformPolyBound inputSize
      (fun input choice ↦ cost input choice (value input choice)) := by
  obtain ⟨costCoefficient, costExponent, hcost⟩ := hcost
  obtain ⟨valueCoefficient, valueExponent, hvalue⟩ := hvalue
  refine ⟨costCoefficient *
      (valueCoefficient + 1) ^ costExponent,
    max 1 valueExponent * costExponent, ?_⟩
  intro input choice
  apply (hcost input choice (value input choice)).trans
  have hsize : inputSize input + valueSize input choice
        (value input choice) + 1 ≤
      (valueCoefficient + 1) *
        (inputSize input + 1) ^ max 1 valueExponent := by
    have hvalue' := hvalue input choice
    have hbase : 1 ≤ inputSize input + 1 := by omega
    have hpow : (inputSize input + 1) ^ valueExponent ≤
        (inputSize input + 1) ^ max 1 valueExponent :=
      Nat.pow_le_pow_right hbase (le_max_right _ _)
    have hself : inputSize input + 1 ≤
        (inputSize input + 1) ^ max 1 valueExponent := by
      simpa using Nat.pow_le_pow_right hbase (le_max_left 1 valueExponent)
    calc
      inputSize input + valueSize input choice (value input choice) + 1
          = (inputSize input + 1) +
              valueSize input choice (value input choice) := by omega
      _ ≤ (inputSize input + 1) +
            valueCoefficient * (inputSize input + 1) ^ valueExponent := by
          exact Nat.add_le_add_left hvalue' _
      _ ≤ (inputSize input + 1) ^ max 1 valueExponent +
            valueCoefficient *
              (inputSize input + 1) ^ max 1 valueExponent := by gcongr
      _ = (valueCoefficient + 1) *
            (inputSize input + 1) ^ max 1 valueExponent := by ring
  calc
    costCoefficient *
          (inputSize input + valueSize input choice (value input choice) + 1) ^
            costExponent
        ≤ costCoefficient *
          ((valueCoefficient + 1) *
            (inputSize input + 1) ^ max 1 valueExponent) ^
              costExponent := by gcongr
    _ = costCoefficient * (valueCoefficient + 1) ^ costExponent *
          (inputSize input + 1) ^
            (max 1 valueExponent * costExponent) := by
          simp only [mul_pow, pow_mul]
          ring

end IsUniformPolyBoundInInputAndValueSize

/-! ## Sequential composition with intermediate-size control -/

namespace CostedImplementation

/-- Compose a costed implementation with a dependent continuation.  The
returned type may depend on the original input, while the continuation may
inspect the intermediate value. -/
def thenCosted
    {Input : Type u} {Intermediate : Input → Type v}
    {Output : Input → Type w}
    {firstFunction : (input : Input) → Intermediate input}
    (first : CostedImplementation firstFunction)
    (secondFunction : (input : Input) → Intermediate input → Output input)
    (secondRun : (input : Input) →
      (intermediate : Intermediate input) → Cost (Output input))
    (secondCorrect : ∀ input intermediate,
      (secondRun input intermediate).value =
        secondFunction input intermediate) :
    CostedImplementation
      (fun input ↦ secondFunction input (firstFunction input)) where
  run input := Cost.bind (first.run input) (secondRun input)
  correct input := by
    rw [Cost.value_bind, secondCorrect, first.correct]

/-- Polynomial-time closure of sequential composition.  Unlike an unsound
time-only rule, this theorem explicitly requires the first result to have
polynomial size and requires one uniform cost polynomial for the
continuation. -/
theorem thenCosted_isPolynomial
    {Input : Type u} {Intermediate : Input → Type v}
    {Output : Input → Type w}
    {inputSize : Input → ℕ}
    {intermediateSize : (input : Input) → Intermediate input → ℕ}
    {firstFunction : (input : Input) → Intermediate input}
    (first : CostedImplementation firstFunction)
    (secondFunction : (input : Input) → Intermediate input → Output input)
    (secondRun : (input : Input) →
      (intermediate : Intermediate input) → Cost (Output input))
    (secondCorrect : ∀ input intermediate,
      (secondRun input intermediate).value =
        secondFunction input intermediate)
    (hfirst : first.IsPolynomial inputSize)
    (hintermediate : HasPolynomialOutputSize inputSize
      intermediateSize firstFunction)
    (hsecond : IsPolyBoundInInputAndValueSize inputSize intermediateSize
      (fun input intermediate ↦ (secondRun input intermediate).ops)) :
    (first.thenCosted secondFunction secondRun secondCorrect).IsPolynomial
      inputSize := by
  rw [hasPolynomialOutputSize_iff] at hintermediate
  have hspecialized := hsecond.specialize firstFunction hintermediate
  show IsPolyBound inputSize (fun input ↦
    (Cost.bind (first.run input) (secondRun input)).ops)
  simpa only [Cost.ops_bind, first.correct] using
    IsPolyBound.add hfirst hspecialized

end CostedImplementation

namespace CostedImplementationWithChoice

/-- Choice-preserving sequential composition.  The same seed/oracle/path is
visible to both stages, so no information is silently added between them. -/
def thenCosted
    {Input : Type u} {Choice : Input → Type v}
    {Intermediate : (input : Input) → Choice input → Type w}
    {Output : (input : Input) → Choice input → Type x}
    {firstFunction : (input : Input) → (choice : Choice input) →
      Intermediate input choice}
    (first : CostedImplementationWithChoice firstFunction)
    (secondFunction : (input : Input) → (choice : Choice input) →
      Intermediate input choice → Output input choice)
    (secondRun : (input : Input) → (choice : Choice input) →
      Intermediate input choice → Cost (Output input choice))
    (secondCorrect : ∀ input choice intermediate,
      (secondRun input choice intermediate).value =
        secondFunction input choice intermediate) :
    CostedImplementationWithChoice
      (fun input choice ↦
        secondFunction input choice (firstFunction input choice)) where
  choice_nonempty := first.choice_nonempty
  run input choice :=
    Cost.bind (first.run input choice) (secondRun input choice)
  correct input choice := by
    rw [Cost.value_bind, secondCorrect, first.correct]

/-- Uniform polynomial-time closure under choice-preserving sequential
composition, including the necessary uniform intermediate-size premise. -/
theorem thenCosted_isPolynomial
    {Input : Type u} {Choice : Input → Type v}
    {Intermediate : (input : Input) → Choice input → Type w}
    {Output : (input : Input) → Choice input → Type x}
    {inputSize : Input → ℕ}
    {intermediateSize : (input : Input) → (choice : Choice input) →
      Intermediate input choice → ℕ}
    {firstFunction : (input : Input) → (choice : Choice input) →
      Intermediate input choice}
    (first : CostedImplementationWithChoice firstFunction)
    (secondFunction : (input : Input) → (choice : Choice input) →
      Intermediate input choice → Output input choice)
    (secondRun : (input : Input) → (choice : Choice input) →
      Intermediate input choice → Cost (Output input choice))
    (secondCorrect : ∀ input choice intermediate,
      (secondRun input choice intermediate).value =
        secondFunction input choice intermediate)
    (hfirst : first.IsPolynomial inputSize)
    (hintermediate : HasUniformPolynomialOutputSize inputSize
      intermediateSize firstFunction)
    (hsecond : IsUniformPolyBoundInInputAndValueSize inputSize
      intermediateSize
      (fun input choice intermediate ↦
        (secondRun input choice intermediate).ops)) :
    (first.thenCosted secondFunction secondRun secondCorrect).IsPolynomial
      inputSize := by
  rw [hasUniformPolynomialOutputSize_iff] at hintermediate
  have hspecialized := hsecond.specialize firstFunction hintermediate
  show IsUniformPolyBound inputSize (fun input choice ↦
    (Cost.bind (first.run input choice) (secondRun input choice)).ops)
  simpa only [Cost.ops_bind, first.correct] using
    IsUniformPolyBound.add hfirst hspecialized

end CostedImplementationWithChoice

/-! ## Reachable-state bounds for loops -/

namespace Cost

/-- Pure state reached after a fixed number of applications of an
instrumented transition. -/
def iterateState (step : α → Cost α) (iterations : ℕ) (initial : α) : α :=
  ((fun state ↦ (step state).value)^[iterations]) initial

@[simp] theorem iterateState_zero (step : α → Cost α) (initial : α) :
    iterateState step 0 initial = initial := rfl

theorem iterateState_succ (step : α → Cost α)
    (iterations : ℕ) (initial : α) :
    iterateState step (iterations + 1) initial =
      iterateState step iterations (step initial).value := by
  simp [iterateState, Function.iterate_succ_apply]

@[simp] theorem value_iterate (iterations : ℕ) (step : α → Cost α)
    (initial : α) :
    (iterate iterations step initial).value =
      iterateState step iterations initial := by
  induction iterations generalizing initial with
  | zero => rfl
  | succ iterations ih =>
      change (iterate iterations step (step initial).value).value =
        iterateState step (iterations + 1) initial
      rw [ih, iterateState_succ]

/-- A counted-loop bound that needs a body-cost hypothesis only at states
actually reached from the selected initial state. -/
theorem ops_iterate_le_reachable
    (iterations bodyBound : ℕ) (step : α → Cost α) (initial : α)
    (hstep : ∀ stage, stage < iterations →
      (step (iterateState step stage initial)).ops ≤ bodyBound) :
    (iterate iterations step initial).ops ≤
      iterations * (bodyBound + 1) := by
  induction iterations generalizing initial with
  | zero =>
      simp [iterate, ops, pure, CostM.pure]
  | succ remaining ih =>
      have hfirst : (step initial).ops ≤ bodyBound := by
        simpa [iterateState] using hstep 0 (by omega)
      have htail : (iterate remaining step (step initial).value).ops ≤
          remaining * (bodyBound + 1) := by
        apply ih
        intro stage hstage
        have h := hstep (stage + 1) (by omega)
        simpa [iterateState, Function.iterate_succ_apply] using h
      simp only [iterate]
      calc
        (step initial).ops +
              (iterate remaining step (step initial).value).ops + 1
            ≤ bodyBound + remaining * (bodyBound + 1) + 1 := by omega
        _ = (remaining + 1) * (bodyBound + 1) := by ring

/-- Reachable-state version of the fuelled-while cost bound.  The hypotheses
follow the sequence obtained by repeatedly applying the body; an actual while
execution is a prefix of this sequence because it stops when its condition is
false. -/
theorem ops_whileFuel_le_reachable
    (fuel conditionBound bodyBound : ℕ)
    (condition : α → Cost Bool) (body : α → Cost α) (initial : α)
    (hcondition : ∀ stage, stage < fuel →
      (condition (iterateState body stage initial)).ops ≤ conditionBound)
    (hbody : ∀ stage, stage < fuel →
      (body (iterateState body stage initial)).ops ≤ bodyBound) :
    (whileFuel fuel condition body initial).ops ≤
      fuel * (conditionBound + bodyBound + 1) := by
  induction fuel generalizing initial with
  | zero =>
      simp [whileFuel, ops, pure, CostM.pure]
  | succ remaining ih =>
      have htest : (condition initial).ops ≤ conditionBound := by
        simpa [iterateState] using hcondition 0 (by omega)
      have hnext : (body initial).ops ≤ bodyBound := by
        simpa [iterateState] using hbody 0 (by omega)
      simp only [whileFuel]
      split
      · have htail :
            (whileFuel remaining condition body (body initial).value).ops ≤
              remaining * (conditionBound + bodyBound + 1) := by
          apply ih
          · intro stage hstage
            have h := hcondition (stage + 1) (by omega)
            simpa [iterateState, Function.iterate_succ_apply] using h
          · intro stage hstage
            have h := hbody (stage + 1) (by omega)
            simpa [iterateState, Function.iterate_succ_apply] using h
        calc
          (condition initial).ops + (body initial).ops +
                (whileFuel remaining condition body
                  (body initial).value).ops + 1
              ≤ conditionBound + bodyBound +
                    remaining * (conditionBound + bodyBound + 1) + 1 := by
                  omega
          _ = (remaining + 1) *
                (conditionBound + bodyBound + 1) := by ring
      · calc
          (condition initial).ops + 1 ≤ conditionBound + 1 := by omega
          _ ≤ conditionBound + bodyBound + 1 := by omega
          _ ≤ (remaining + 1) *
                (conditionBound + bodyBound + 1) := by
              exact Nat.le_mul_of_pos_left _ (Nat.succ_pos remaining)

end Cost

/-- A polynomial majorant for all states reached during a counted iteration.
Stage `0` is the initial state and stage `iterations input` is the final
state. -/
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

/-- A local operation count that is polynomial uniformly in the original
input size and the current state size. -/
abbrev IsPolyBoundInInputAndStateSize :=
  @IsPolyBoundInInputAndValueSize

/-- Counted iteration is polynomial when the iteration count is polynomial,
all reachable states have polynomial size, and one common local polynomial
controls the body cost in input-and-state size. -/
theorem isPolyTime_iterate_of_reachableStateSize
    {Input : Type u} {State : Input → Type v}
    {sizeOf : Input → ℕ}
    {stateSize : (input : Input) → State input → ℕ}
    {iterations : Input → ℕ}
    {step : (input : Input) → State input → Cost (State input)}
    {initial : (input : Input) → State input}
    (hiterations : IsPolyBound sizeOf iterations)
    (states : IterateStateSizeCertificate
      sizeOf stateSize iterations step initial)
    (hstep : IsPolyBoundInInputAndStateSize sizeOf stateSize
      (fun input state ↦ (step input state).ops)) :
    IsPolyTime sizeOf fun input ↦
      Cost.iterate (iterations input) (step input) (initial input) := by
  obtain ⟨coefficient, exponent, hlocal⟩ := hstep
  let bodyBound : Input → ℕ := fun input ↦
    coefficient *
      (sizeOf input + states.bound input + 1) ^ exponent
  have hbase : IsPolyBound sizeOf fun input ↦
      sizeOf input + states.bound input + 1 :=
    IsPolyBound.add
      (IsPolyBound.add (IsPolyBound.self (sizeOf := sizeOf))
        states.bound_isPolynomial)
      (IsPolyBound.const 1)
  have hbodyBound : IsPolyBound sizeOf bodyBound := by
    exact IsPolyBound.mul (IsPolyBound.const coefficient)
      (IsPolyBound.pow hbase exponent)
  have htotal : IsPolyBound sizeOf fun input ↦
      iterations input * (bodyBound input + 1) :=
    IsPolyBound.mul hiterations
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1))
  apply IsPolyBound.of_le htotal
  intro input
  apply Cost.ops_iterate_le_reachable
  intro stage hstage
  apply (hlocal input
    (Cost.iterateState (step input) stage (initial input))).trans
  have hstate := states.state_le input stage (Nat.le_of_lt hstage)
  dsimp [bodyBound]
  gcongr

/-- Fuelled while loops satisfy the same reachable-state principle.  The
state certificate follows repeated body transitions, which over-approximates
every actual execution prefix. -/
theorem isPolyTime_whileFuel_of_reachableStateSize
    {Input : Type u} {State : Input → Type v}
    {sizeOf : Input → ℕ}
    {stateSize : (input : Input) → State input → ℕ}
    {fuel : Input → ℕ}
    {condition : (input : Input) → State input → Cost Bool}
    {body : (input : Input) → State input → Cost (State input)}
    {initial : (input : Input) → State input}
    (hfuel : IsPolyBound sizeOf fuel)
    (states : IterateStateSizeCertificate
      sizeOf stateSize fuel body initial)
    (hcondition : IsPolyBoundInInputAndStateSize sizeOf stateSize
      (fun input state ↦ (condition input state).ops))
    (hbody : IsPolyBoundInInputAndStateSize sizeOf stateSize
      (fun input state ↦ (body input state).ops)) :
    IsPolyTime sizeOf fun input ↦
      Cost.whileFuel (fuel input) (condition input) (body input)
        (initial input) := by
  obtain ⟨conditionCoefficient, conditionExponent, hcondition⟩ := hcondition
  obtain ⟨bodyCoefficient, bodyExponent, hbody⟩ := hbody
  let conditionBound : Input → ℕ := fun input ↦
    conditionCoefficient *
      (sizeOf input + states.bound input + 1) ^ conditionExponent
  let bodyBound : Input → ℕ := fun input ↦
    bodyCoefficient *
      (sizeOf input + states.bound input + 1) ^ bodyExponent
  have hbase : IsPolyBound sizeOf fun input ↦
      sizeOf input + states.bound input + 1 :=
    IsPolyBound.add
      (IsPolyBound.add (IsPolyBound.self (sizeOf := sizeOf))
        states.bound_isPolynomial)
      (IsPolyBound.const 1)
  have hconditionBound : IsPolyBound sizeOf conditionBound := by
    exact IsPolyBound.mul (IsPolyBound.const conditionCoefficient)
      (IsPolyBound.pow hbase conditionExponent)
  have hbodyBound : IsPolyBound sizeOf bodyBound := by
    exact IsPolyBound.mul (IsPolyBound.const bodyCoefficient)
      (IsPolyBound.pow hbase bodyExponent)
  have hperIteration : IsPolyBound sizeOf fun input ↦
      conditionBound input + bodyBound input + 1 :=
    IsPolyBound.add
      (IsPolyBound.add hconditionBound hbodyBound)
      (IsPolyBound.const 1)
  have htotal : IsPolyBound sizeOf fun input ↦
      fuel input *
        (conditionBound input + bodyBound input + 1) :=
    IsPolyBound.mul hfuel hperIteration
  apply IsPolyBound.of_le htotal
  intro input
  apply Cost.ops_whileFuel_le_reachable
  · intro stage hstage
    apply (hcondition input
      (Cost.iterateState (body input) stage (initial input))).trans
    have hstate := states.state_le input stage (Nat.le_of_lt hstage)
    dsimp [conditionBound]
    gcongr
  · intro stage hstage
    apply (hbody input
      (Cost.iterateState (body input) stage (initial input))).trans
    have hstate := states.state_le input stage (Nat.le_of_lt hstage)
    dsimp [bodyBound]
    gcongr

end EconCSLib.OpenProblem.UnitCostRAM
