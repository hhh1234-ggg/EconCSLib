# Unit-cost real-RAM complexity definitions

This framework deliberately separates two definitions:

1. the exact resource usage of one execution; and
2. the proposition that the resulting resource function has a polynomial
   upper bound.

It does not contain a procedure that reads arbitrary Lean source code and
decides whether it is polynomial-time.

## Module layout

The implementation is split into two one-way layers under
`EconCSLib.OpenProblem.Util.Complexity`:

```text
Definitions/
  UnitCostRAM.lean
  UnitCostRAMMachine.lean
  SizeGrowth.lean
  Interfaces.lean

Support/
  UnitCostRAM.lean
  UnitCostRAMMachine.lean
  SizeGrowth.lean
  Interfaces.lean
```

`Definitions/` contains the data types, operational semantics, exact resource
functions, and propositions that state polynomial boundedness.  It has no
named theorem, lemma, or example, and it never imports `Support/`.

`Support/` imports `Definitions/` and supplies simp lemmas, closure theorems,
certificate constructors, traversal and loop combinators, composition
results, and canonical-output proofs.  Thus a problem statement that only
needs the vocabulary can import `Complexity.Definitions.Interfaces`, while a
proof that needs the full library can import `Complexity.Support.Interfaces`.

The historical modules `UnitCostRAM`, `UnitCostRAMMachine`, `SizeGrowth`, and
`Complexity` remain as import-only facades that re-export both layers, so this
reorganization does not change existing public declaration names.

## 1. Exact execution cost

`EconCSLib.OpenProblem.Util.UnitCostRAMMachine` defines a finite
instruction-level RAM. A word is an exact integer, exact real, or Boolean.
Inputs and outputs use lossless encodings into finite lists of words.

The interpreter, rather than the program author, assigns the cost of every
executed instruction:

| Instruction | Local-step charge | Additional counter |
| --- | ---: | --- |
| scalar arithmetic, comparison, move, load, store, jump, branch | `1` | none |
| `allocate k`, `free k` | `k + 1` | peak live cells |
| halt with `k` output words | `k + 1` | none |
| oracle call with `a` argument and `b` answer words | `a + b + 1` | one oracle query |
| sample call with `a` parameter and `b` result words | `a + b + 1` | one sample |
| random-bit read | `1` | one random bit |

Faulting instructions are still charged. Insufficient fuel, a machine fault,
and successful halt are distinct execution results.

For one concrete run, `ProfiledCost.exactResourceUsage` returns:

```lean
structure ExactResourceUsage where
  localSteps : ℕ
  oracleQueries : ℕ
  distributionSamples : ℕ
  randomBits : ℕ
  communicationUnits : ℕ
  peakAuxiliaryCells : ℕ
```

The strict machine currently generates the first four counters and dynamic
allocation data directly. Communication protocols have their own structural
counter in `Complexity.lean`; a strict RAM computation does not silently infer
communication from arbitrary Lean functions.

### Deterministic functions

`FixedEncodingRAMImplementation` contains fixed input/output encodings, one
finite closed program, fuel, and canonical correctness. It makes no
asymptotic claim. Its counting functions are:

```lean
implementation.execution input
implementation.operationCount input
implementation.resourceUsage input
implementation.standardResourceCount resource input
```

`operationCount` is exactly the local-step projection of `execution`.

### Oracles, random tapes, and adversarial choices

`FixedEnvironmentRAMImplementation` fixes the operation type and environment
outside the program witness. Its exact counters depend on both the ordinary
input and an execution choice:

```lean
implementation.operationCount input choice
implementation.resourceUsage input choice
```

This layer counts each selected trace. A probability distribution, fair-bit
law, sampling kernel, or bounded-error condition is separate semantic data;
it is not invented by the cost definition.

The interpreter counts an external call and all transferred words, but not
the internal implementation of `environment.external`. Such an operation is
therefore an oracle boundary unless a separate machine-level implementation
and composition theorem are supplied.

### Promise search problems

`FixedEncodingRAMSearchImplementation` uses the same execution semantics, but
correctness and asymptotic bounds are required only for inputs satisfying an
explicit promise.

## 2. Polynomial boundedness

For an arbitrary input type and arbitrary natural-valued cost function, the
basic definition is:

```lean
def IsPolyBound (sizeOf : Input → ℕ) (cost : Input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input,
      cost input ≤ coefficient * (sizeOf input + 1) ^ exponent
```

Thus “polynomial” means only the existence of one uniform upper bound. It does
not mean that `cost` is itself a polynomial, that the exponent is optimal, or
that a matching lower bound exists.

The promise version is:

```lean
∃ coefficient exponent : ℕ,
  ∀ input, valid input →
    cost input ≤ coefficient * (sizeOf input + 1) ^ exponent
```

The choice-uniform version places the constants before both input and choice:

```lean
∃ coefficient exponent : ℕ,
  ∀ input choice,
    cost input choice ≤ coefficient * (sizeOf input + 1) ^ exponent
```

Consequently an adversarial choice, oracle implementation, seed, or random
tape cannot select its own coefficient or exponent.

For a fixed list of nonnegative size parameters, `IsPolyBoundInSizes` uses
their sum as the scalar size. When parameter names must be retained,
`IsMvPolynomialBound` instead asks for one
`MvPolynomial Parameter ℕ` majorant. These are equivalent for a fixed finite
parameter type, but the latter records expressions such as `V * E` directly.

Expected cost is a nonnegative real-valued function and is polynomially
bounded when the same coefficient and exponent bound that expectation. This
definition is used only when the problem explicitly asks for expected rather
than worst-case complexity.

## 3. Combining the two definitions

For deterministic strict implementations:

```lean
implementation.IsPolynomialTime :=
  IsPolyBound inputEncoding.size implementation.operationCount
```

For fixed-environment implementations the uniform version is used, and for
promise search implementations the promise-restricted version is used.

The bundled structures `StrictRAMComputableInPolyTime`,
`StrictRAMComputableInPolyTimeWithFixedEnvironment`, and
`StrictRAMSearchableInPolyTime` merely package:

- one finite strict program;
- canonical correctness of the same execution being counted; and
- explicit natural numbers `coefficient` and `exponent` with the appropriate
  inequality.

No Boolean classifier or symbolic growth-expression language is involved.

## 4. Representations and trust boundaries

Input and output encodings are parameters fixed before the program witness.
Correctness requires the machine to emit exactly the canonical encoded
output, rather than an arbitrary alias accepted by a decoder. This permits
strict programs and strict reductions to compose at the word-list level.

The framework cannot determine that an arbitrary mathematical encoding is an
appropriate representation of a particular problem. A `Problem.lean` file
must use a canonical structural encoding fixed independently of the solver;
it must not encode the desired answer or perform hidden computation in the
representation itself.

Similarly, declaring exact integer or real arithmetic to cost one step is the
chosen unit-cost RAM/BSS model, not a theorem about processor time. A problem
requiring Turing bit complexity must instead use binary words and charge
arithmetic according to operand length.

The compositional `CostM` interfaces in `UnitCostRAM.lean` remain useful for
proofs, but their annotations are trusted: `Cost.pure` or an arbitrary Lean
callback can hide work. Complexity-class statements should use the strict
instruction interpreter whenever operational enforcement is required.

## 5. Problem-facing definitions

The usual `Problem.lean` interface needs only:

```text
FixedEncodingRAMImplementation
FixedEnvironmentRAMImplementation
FixedEncodingRAMSearchImplementation

operationCount
resourceUsage
standardResourceCount

PolynomialCostBound
PolynomialCostBoundOn
UniformPolynomialCostBound
UniformPolynomialCostBoundOn
MultivariatePolynomialCostBound
PolynomialExpectedCostBound

FunctionRunsInFixedEncodingStrictRAMPolynomialTime
FunctionRunsInFixedEncodingStrictRAMPolynomialTimeUniformly
SearchRunsInFixedEncodingStrictRAMPolynomialTimeOn
```

Search reductions additionally fix all four encodings and require both strict
programs to emit canonical outputs, so there is no uncharged normalization
step between reductions.

## References

- S. A. Cook and R. A. Reckhow, “Time Bounded Random Access Machines,” 1973.
- L. Blum, M. Shub, and S. Smale, “On a Theory of Computation and Complexity
  over the Real Numbers,” 1989.
- Mathlib, `Algebra.Polynomial` and `Algebra.MvPolynomial`.
