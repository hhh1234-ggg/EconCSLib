/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import EconCSLib.Foundation.CostM.Cells
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Real.Basic

/-!
# Foundational unit-cost RAM definitions

This module contains only the foundational vocabulary and semantic definitions
for unit-cost RAM accounting.  Named proof lemmas, traversal libraries,
polynomial-closure rules, and operational convenience combinators live in
`Complexity.Support.UnitCostRAM`.

`Cost` and `ProfiledCost` are instrumentation interfaces.  Their zero-cost
constructors and arbitrary Lean callbacks are trusted accounting boundaries.
Machine-enforced complexity statements should use `UnitCostRAMMachine`.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM

universe u v w

/-! ## Unit-cost computations -/

/-- Unit-cost RAM computations are the natural-number specialization of the
shared `CostM` writer monad. -/
abbrev Cost (α : Type u) := CostM ℕ α

namespace Cost

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Compatibility projection for the returned value of a unit-cost
computation. -/
@[simp] def value (x : Cost α) : α := x.ret

/-- Compatibility projection for the number of charged RAM operations. -/
@[simp] def ops (x : Cost α) : ℕ := x.cost

/-- Inject an already available value without charging an operation.

This constructor is a trusted accounting boundary: Lean evaluates its argument
outside the writer cost. -/
def pure (a : α) : Cost α := CostM.pure a

/-- Sequential composition; only the two component computations contribute
to the operation count. -/
def bind (x : Cost α) (f : α → Cost β) : Cost β :=
  let y := f x.value
  ⟨y.value, x.ops + y.ops⟩

/-- Apply a bookkeeping-only transformation without adding a RAM charge. -/
def map (f : α → β) (x : Cost α) : Cost β := ⟨f x.value, x.ops⟩

/-- Applicative sequencing with additive operation counts. -/
def seq (f : Cost (α → β)) (x : Unit → Cost α) : Cost β :=
  let x := x ()
  ⟨f.value x.value, f.ops + x.ops⟩

/-- Charge one operation after an already instrumented computation. -/
def tick (x : Cost α) : Cost α := ⟨x.value, x.ops + 1⟩

/-- A unary primitive operation costs one unit. -/
def liftUnary (op : α → β) (x : Cost α) : Cost β :=
  ⟨op x.value, x.ops + 1⟩

/-- A binary primitive operation costs one unit in addition to the cost of
obtaining its operands. -/
def liftBinary (op : α → β → γ) (x : Cost α) (y : Cost β) : Cost γ :=
  ⟨op x.value y.value, x.ops + y.ops + 1⟩

/-- A ternary primitive operation costs one unit in addition to its operands. -/
def liftTernary {δ : Type*} (op : α → β → γ → δ)
    (x : Cost α) (y : Cost β) (z : Cost γ) : Cost δ :=
  ⟨op x.value y.value z.value, x.ops + y.ops + z.ops + 1⟩

def add [Add α] (x y : Cost α) : Cost α := liftBinary (· + ·) x y
def sub [Sub α] (x y : Cost α) : Cost α := liftBinary (· - ·) x y
def mul [Mul α] (x y : Cost α) : Cost α := liftBinary (· * ·) x y
def div [Div α] (x y : Cost α) : Cost α := liftBinary (· / ·) x y
def neg [Neg α] (x : Cost α) : Cost α := liftUnary Neg.neg x

def le [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (x y : Cost α) : Cost Bool :=
  liftBinary (fun a b => decide (a ≤ b)) x y

def lt [LT α] [DecidableRel ((· < ·) : α → α → Prop)]
    (x y : Cost α) : Cost Bool :=
  liftBinary (fun a b => decide (a < b)) x y

def beq [DecidableEq α] (x y : Cost α) : Cost Bool :=
  liftBinary (fun a b => decide (a = b)) x y

/-- A branch decision costs one unit after the condition has been computed;
only the selected branch is executed. -/
def branch (condition : Cost Bool) (ifTrue ifFalse : Unit → Cost α) : Cost α :=
  let result := if condition.value then ifTrue () else ifFalse ()
  ⟨result.value, condition.ops + result.ops + 1⟩

/-! ## Unit-cost random-access memory -/

/-- Unbounded mathematical RAM memory. -/
abbrev Memory (Word : Type*) := ℕ → Word

/-- Reading one addressed cell costs one unit. -/
def readMemory {Word : Type*}
    (memory : Cost (Memory Word)) (address : Cost ℕ) : Cost Word :=
  liftBinary (fun m i => m i) memory address

/-- Writing one addressed cell costs one unit and returns the updated memory. -/
def writeMemory {Word : Type*}
    (memory : Cost (Memory Word)) (address : Cost ℕ) (word : Cost Word) :
    Cost (Memory Word) :=
  liftTernary (fun m i value => Function.update m i value)
    memory address word

end Cost

/-! ## Unit-cost words and fixed encodings -/

/-- One externally represented word.  Exact real words use the BSS/unit-cost
real-RAM convention rather than bit approximation. -/
inductive Word
  | integer (value : Int)
  | real (value : ℝ)
  | bit (value : Bool)

/-- A lossless finite-word representation of an input type. -/
structure Encoding (Input : Type u) where
  encode : Input → List Word
  decode : List Word → Option Input
  decode_encode : ∀ input, decode (encode input) = some input

/-- Number of unit-cost RAM words in an encoded input. -/
def Encoding.size {Input : Type u} (encoding : Encoding Input)
    (input : Input) : ℕ := (encoding.encode input).length

/-- Lossless representation of an output type that depends on its input. -/
structure DependentEncoding {Input : Type u} (Output : Input → Type v) where
  encode : (input : Input) → Output input → List Word
  decode : (input : Input) → List Word → Option (Output input)
  decode_encode : ∀ input output, decode input (encode input output) = some output

def DependentEncoding.size {Input : Type u} {Output : Input → Type v}
    (encoding : DependentEncoding Output) (input : Input)
    (output : Output input) : ℕ := (encoding.encode input output).length

namespace DependentEncoding

/-- Pull a dependent encoding back along a change of input index. -/
def comap {Input : Type u} {Index : Type v} {Output : Input → Type w}
    (encoding : DependentEncoding Output) (index : Index → Input) :
    DependentEncoding (fun i => Output (index i)) where
  encode i output := encoding.encode (index i) output
  decode i words := encoding.decode (index i) words
  decode_encode i output := encoding.decode_encode (index i) output

end DependentEncoding

namespace Encoding

/-- Regard an ordinary encoding as an input-independent dependent encoding. -/
def dependent {Index : Type v} {Value : Type u}
    (encoding : Encoding Value) :
    DependentEncoding (fun _ : Index => Value) where
  encode _ value := encoding.encode value
  decode _ words := encoding.decode words
  decode_encode _ value := encoding.decode_encode value

/-- Canonical length-prefixed encoding of a dependent pair. -/
def sigma {Input : Type u} {Output : Input → Type v}
    (input : Encoding Input) (output : DependentEncoding Output) :
    Encoding (Σ i, Output i) where
  encode pair :=
    .integer (input.encode pair.1).length ::
      input.encode pair.1 ++ output.encode pair.1 pair.2
  decode words :=
    match words with
    | .integer length :: rest =>
        if 0 ≤ length then
          let count := length.toNat
          match input.decode (rest.take count) with
          | some i =>
              match output.decode i (rest.drop count) with
              | some value => some ⟨i, value⟩
              | none => none
          | none => none
        else none
    | _ => none
  decode_encode pair := by
    simp [input.decode_encode, output.decode_encode]

end Encoding

/-! ## Simultaneous exact resource accounting -/

/-- Additive resources accumulated by a sequential unit-cost RAM run. -/
@[ext]
structure ResourceCounts where
  steps : ℕ
  oracleQueries : ℕ
  distributionSamples : ℕ
  randomBits : ℕ
  communicationUnits : ℕ
  deriving DecidableEq

namespace ResourceCounts

instance : Zero ResourceCounts := ⟨⟨0, 0, 0, 0, 0⟩⟩

instance : Add ResourceCounts where
  add left right :=
    ⟨left.steps + right.steps,
      left.oracleQueries + right.oracleQueries,
      left.distributionSamples + right.distributionSamples,
      left.randomBits + right.randomBits,
      left.communicationUnits + right.communicationUnits⟩

instance : AddCommMonoid ResourceCounts where
  add_assoc _ _ _ := by ext <;> exact Nat.add_assoc _ _ _
  zero_add _ := by ext <;> exact Nat.zero_add _
  add_zero _ := by ext <;> exact Nat.add_zero _
  add_comm _ _ := by ext <;> exact Nat.add_comm _ _
  nsmul := nsmulRec

/-- One ordinary unit-cost RAM instruction. -/
def localStep : ResourceCounts := ⟨1, 0, 0, 0, 0⟩

/-- A block of ordinary unit-cost RAM instructions. -/
def localSteps (steps : ℕ) : ResourceCounts := ⟨steps, 0, 0, 0, 0⟩

/-- One unit-time oracle invocation. -/
def oracleQuery : ResourceCounts := ⟨1, 1, 0, 0, 0⟩

/-- One oracle invocation plus argument and answer transfer. -/
def oracleQueryTransfer (argumentWords answerWords : ℕ) : ResourceCounts :=
  ⟨argumentWords + answerWords + 1, 1, 0, 0, 0⟩

/-- One call to a distribution-sampling oracle. -/
def distributionSample : ResourceCounts := ⟨1, 0, 1, 0, 0⟩

/-- One sample invocation plus parameter and sample transfer. -/
def distributionSampleTransfer
    (parameterWords sampleWords : ℕ) : ResourceCounts :=
  ⟨parameterWords + sampleWords + 1, 0, 1, 0, 0⟩

/-- Reading `bits` random bits, also charged as one local action. -/
def randomness (bits : ℕ) : ResourceCounts := ⟨1, 0, 0, bits, 0⟩

/-- Sending a message of the advertised unit length. -/
def communication (units : ℕ) : ResourceCounts := ⟨1, 0, 0, 0, units⟩

end ResourceCounts

/-- A profiled computation with additive resources and peak live memory. -/
abbrev ProfiledCost (α : Type u) := CostM (ResourceCounts × Cells) α

namespace ProfiledCost

variable {α : Type u} {β : Type v}

/-- Return a value with no resource charge. -/
def pure (value : α) : ProfiledCost α := CostM.pure value

/-- Charge an arbitrary, auditable resource vector and memory event. -/
def charge (resources : ResourceCounts) (cells : Cells) (value : α) :
    ProfiledCost α := ⟨value, (resources, cells)⟩

/-- One ordinary unit-cost RAM operation. -/
def localOperation (operation : α → β)
    (input : ProfiledCost α) : ProfiledCost β :=
  ⟨operation input.ret, input.cost + (ResourceCounts.localStep, 0)⟩

/-- Invoke an oracle once. -/
def oracleCall {Query Answer : Type*} (oracle : Query → Answer)
    (query : ProfiledCost Query) : ProfiledCost Answer :=
  ⟨oracle query.ret, query.cost + (ResourceCounts.oracleQuery, 0)⟩

/-- Draw once from an externally supplied distribution sampler. -/
def sampleCall {Parameter Sample : Type*} (sampler : Parameter → Sample)
    (parameter : ProfiledCost Parameter) : ProfiledCost Sample :=
  ⟨sampler parameter.ret,
    parameter.cost + (ResourceCounts.distributionSample, 0)⟩

/-- Consume supplied random bits. Probability laws remain separate data. -/
def consumeRandomBits (bits : List Bool) : ProfiledCost (List Bool) :=
  charge (ResourceCounts.randomness bits.length) 0 bits

/-- Send a bitstring and return it unchanged. -/
def send (message : List Bool) : ProfiledCost (List Bool) :=
  charge (ResourceCounts.communication message.length) 0 message

/-- Send exact unit-cost RAM words. -/
def sendWords (message : List Word) : ProfiledCost (List Word) :=
  charge (ResourceCounts.communication message.length) 0 message

/-- Allocate live RAM words. -/
def alloc (cells : ℕ) : ProfiledCost PUnit :=
  charge 0 (Cells.alloc cells) ()

/-- Release live RAM words. -/
def free (cells : ℕ) : ProfiledCost PUnit :=
  charge 0 (Cells.free cells) ()

def steps (run : ProfiledCost α) : ℕ := run.cost.1.steps
def oracleQueries (run : ProfiledCost α) : ℕ := run.cost.1.oracleQueries
def distributionSamples (run : ProfiledCost α) : ℕ :=
  run.cost.1.distributionSamples
def randomBits (run : ProfiledCost α) : ℕ := run.cost.1.randomBits
def communicationUnits (run : ProfiledCost α) : ℕ :=
  run.cost.1.communicationUnits

/-- Compatibility projection when each communication unit is one bit. -/
def communicatedBits (run : ProfiledCost α) : ℕ := communicationUnits run

def peakCells (run : ProfiledCost α) : ℕ := Int.toNat run.cost.2.peak

/-- The standard resources extracted from one concrete instrumented run. -/
@[ext]
structure ExactResourceUsage where
  localSteps : ℕ
  oracleQueries : ℕ
  distributionSamples : ℕ
  randomBits : ℕ
  communicationUnits : ℕ
  peakAuxiliaryCells : ℕ
  deriving DecidableEq, Repr

/-- Named coordinates of `ExactResourceUsage`. -/
inductive StandardResource where
  | localSteps
  | oracleQueries
  | distributionSamples
  | randomBits
  | communicationUnits
  | peakAuxiliaryCells
  deriving DecidableEq, Repr

/-- Read all standard resource counters from one concrete run. -/
def exactResourceUsage (run : ProfiledCost α) : ExactResourceUsage where
  localSteps := steps run
  oracleQueries := oracleQueries run
  distributionSamples := distributionSamples run
  randomBits := randomBits run
  communicationUnits := communicationUnits run
  peakAuxiliaryCells := peakCells run

/-- Select one named coordinate of an exact resource-usage record. -/
def ExactResourceUsage.get (usage : ExactResourceUsage) :
    StandardResource → ℕ
  | .localSteps => usage.localSteps
  | .oracleQueries => usage.oracleQueries
  | .distributionSamples => usage.distributionSamples
  | .randomBits => usage.randomBits
  | .communicationUnits => usage.communicationUnits
  | .peakAuxiliaryCells => usage.peakAuxiliaryCells

end ProfiledCost

/-! ## Polynomial-bound predicates -/

/-- A natural-valued cost is uniformly polynomially bounded in the chosen
scalar input size. -/
def IsPolyBound {Input : Type u}
    (sizeOf : Input → ℕ) (cost : Input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input, cost input ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Aggregate a fixed list of size parameters. -/
def aggregateSize (sizes : List ℕ) : ℕ := sizes.sum

/-- Polynomial boundedness for a vector of size parameters. -/
def IsPolyBoundInSizes {Input : Type u}
    (sizes : Input → List ℕ) (cost : Input → ℕ) : Prop :=
  IsPolyBound (fun input => aggregateSize (sizes input)) cost

/-- Polynomial boundedness restricted to a promise domain. -/
def IsPolyBoundOn {Input : Type u}
    (valid : Input → Prop) (sizeOf : Input → ℕ) (cost : Input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input, valid input →
      cost input ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size version of `IsPolyBoundOn`. -/
def IsPolyBoundInSizesOn {Input : Type u}
    (valid : Input → Prop) (sizes : Input → List ℕ)
    (cost : Input → ℕ) : Prop :=
  IsPolyBoundOn valid (fun input => aggregateSize (sizes input)) cost

/-- Polynomial operation count for a family of costed computations. -/
def IsPolyTime {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ) (run : (input : Input) → Cost (Output input)) : Prop :=
  IsPolyBound sizeOf (fun input => (run input).ops)

/-- Multivariate-size version of `IsPolyTime`. -/
def IsPolyTimeInSizes {Input : Type u} {Output : Input → Type v}
    (sizes : Input → List ℕ) (run : (input : Input) → Cost (Output input)) : Prop :=
  IsPolyBoundInSizes sizes (fun input => (run input).ops)

/-- Uniform polynomial bound over an adversarial seed, oracle, or path. -/
def IsUniformPolyBound
    {Input : Type u} {Choice : Input → Type v}
    (sizeOf : Input → ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input choice,
      cost input choice ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size version of `IsUniformPolyBound`. -/
def IsUniformPolyBoundInSizes
    {Input : Type u} {Choice : Input → Type v}
    (sizes : Input → List ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  IsUniformPolyBound (fun input => aggregateSize (sizes input)) cost

/-- Uniform polynomial boundedness restricted to legal auxiliary choices. -/
def IsUniformPolyBoundOn
    {Input : Type u} {Choice : Input → Type v}
    (valid : (input : Input) → Choice input → Prop)
    (sizeOf : Input → ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ input choice, valid input choice →
      cost input choice ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size version of `IsUniformPolyBoundOn`. -/
def IsUniformPolyBoundInSizesOn
    {Input : Type u} {Choice : Input → Type v}
    (valid : (input : Input) → Choice input → Prop)
    (sizes : Input → List ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  IsUniformPolyBoundOn valid
    (fun input => aggregateSize (sizes input)) cost

/-! ## Trusted generic function interfaces

These structures define semantic interfaces for author-supplied `CostM`
instrumentation.  They are definitions, not machine-enforced complexity
certificates: `Cost.pure`, `Cost.map`, and arbitrary callbacks can hide work.
-/

/-- Trusted cost instrumentation of a dependent Lean function. -/
structure CostedImplementation
    {Input : Type u} {Output : Input → Type v}
    (function : (input : Input) → Output input) where
  run : (input : Input) → Cost (Output input)
  correct : ∀ input, (run input).value = function input

/-- Trusted cost instrumentation restricted to a promise domain. -/
structure CostedImplementationOn
    {Input : Type u} {Output : Input → Type v}
    (valid : Input → Prop)
    (function : (input : Input) → Output input) where
  run : (input : Input) → Cost (Output input)
  correct : ∀ input, valid input → (run input).value = function input

/-- Trusted cost instrumentation for a dependent search relation. -/
structure CostedSearchImplementation
    {Input : Type u} {Output : Input → Type v}
    (solution : (input : Input) → Output input → Prop) where
  run : (input : Input) → Cost (Output input)
  correct : ∀ input, solution input (run input).value

def CostedImplementation.IsPolynomial
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (implementation : CostedImplementation function)
    (sizeOf : Input → ℕ) : Prop :=
  IsPolyBound sizeOf (fun input => (implementation.run input).ops)

def CostedImplementation.IsPolynomialInSizes
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (implementation : CostedImplementation function)
    (sizes : Input → List ℕ) : Prop :=
  IsPolyBoundInSizes sizes (fun input => (implementation.run input).ops)

def CostedImplementationOn.IsPolynomial
    {Input : Type u} {Output : Input → Type v}
    {valid : Input → Prop} {function : (input : Input) → Output input}
    (implementation : CostedImplementationOn valid function)
    (sizeOf : Input → ℕ) : Prop :=
  IsPolyBoundOn valid sizeOf (fun input => (implementation.run input).ops)

def CostedImplementationOn.IsPolynomialInSizes
    {Input : Type u} {Output : Input → Type v}
    {valid : Input → Prop} {function : (input : Input) → Output input}
    (implementation : CostedImplementationOn valid function)
    (sizes : Input → List ℕ) : Prop :=
  IsPolyBoundInSizesOn valid sizes
    (fun input => (implementation.run input).ops)

def CostedSearchImplementation.IsPolynomial
    {Input : Type u} {Output : Input → Type v}
    {solution : (input : Input) → Output input → Prop}
    (implementation : CostedSearchImplementation solution)
    (sizeOf : Input → ℕ) : Prop :=
  IsPolyBound sizeOf (fun input => (implementation.run input).ops)

def CostedSearchImplementation.IsPolynomialInSizes
    {Input : Type u} {Output : Input → Type v}
    {solution : (input : Input) → Output input → Prop}
    (implementation : CostedSearchImplementation solution)
    (sizes : Input → List ℕ) : Prop :=
  IsPolyBoundInSizes sizes (fun input => (implementation.run input).ops)

def RunsInPolynomialTime
    {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ) (function : (input : Input) → Output input) : Prop :=
  ∃ implementation : CostedImplementation function,
    implementation.IsPolynomial sizeOf

def RunsInPolynomialTimeInSizes
    {Input : Type u} {Output : Input → Type v}
    (sizes : Input → List ℕ) (function : (input : Input) → Output input) : Prop :=
  ∃ implementation : CostedImplementation function,
    implementation.IsPolynomialInSizes sizes

def RunsInPolynomialTimeOn
    {Input : Type u} {Output : Input → Type v}
    (valid : Input → Prop) (sizeOf : Input → ℕ)
    (function : (input : Input) → Output input) : Prop :=
  ∃ implementation : CostedImplementationOn valid function,
    implementation.IsPolynomial sizeOf

def RunsInPolynomialTimeInSizesOn
    {Input : Type u} {Output : Input → Type v}
    (valid : Input → Prop) (sizes : Input → List ℕ)
    (function : (input : Input) → Output input) : Prop :=
  ∃ implementation : CostedImplementationOn valid function,
    implementation.IsPolynomialInSizes sizes

def SearchRunsInPolynomialTime
    {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ)
    (solution : (input : Input) → Output input → Prop) : Prop :=
  ∃ implementation : CostedSearchImplementation solution,
    implementation.IsPolynomial sizeOf

def SearchRunsInPolynomialTimeInSizes
    {Input : Type u} {Output : Input → Type v}
    (sizes : Input → List ℕ)
    (solution : (input : Input) → Output input → Prop) : Prop :=
  ∃ implementation : CostedSearchImplementation solution,
    implementation.IsPolynomialInSizes sizes

def RunsInPolynomialTime₂
    {α : Type u} {β : Type v} {γ : Type w}
    (sizeOf : α × β → ℕ) (function : α → β → γ) : Prop :=
  RunsInPolynomialTime sizeOf (fun input => function input.1 input.2)

/-- Trusted cost instrumentation with an auxiliary execution choice. -/
structure CostedImplementationWithChoice
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) where
  choice_nonempty : ∀ input, Nonempty (Choice input)
  run : (input : Input) →
    (choice : Choice input) → Cost (Output input choice)
  correct : ∀ input choice,
    (run input choice).value = function input choice

def CostedImplementationWithChoice.IsPolynomial
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : CostedImplementationWithChoice function)
    (sizeOf : Input → ℕ) : Prop :=
  IsUniformPolyBound sizeOf
    (fun input choice => (implementation.run input choice).ops)

def CostedImplementationWithChoice.IsPolynomialInSizes
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : CostedImplementationWithChoice function)
    (sizes : Input → List ℕ) : Prop :=
  IsUniformPolyBoundInSizes sizes
    (fun input choice => (implementation.run input choice).ops)

def RunsInPolynomialTimeUniformly
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (sizeOf : Input → ℕ)
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) : Prop :=
  ∃ implementation : CostedImplementationWithChoice function,
    implementation.IsPolynomial sizeOf

def RunsInPolynomialTimeInSizesUniformly
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (sizes : Input → List ℕ)
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) : Prop :=
  ∃ implementation : CostedImplementationWithChoice function,
    implementation.IsPolynomialInSizes sizes

/-- A concrete query-count function is polynomially bounded. -/
abbrev UsesPolynomiallyManyQueries := @IsPolyBound

/-- A concrete communication-count function is polynomially bounded. -/
abbrev UsesPolynomialCommunication := @IsPolyBound

end EconCSLib.OpenProblem.UnitCostRAM
