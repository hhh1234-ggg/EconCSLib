/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity.Definitions.UnitCostRAM

/-!
# An instruction-level unit-cost real-RAM

`CostM` is convenient for compositional proofs, but its annotations are
necessarily trusted: an author could put an expensive Lean term inside
`Cost.pure`.  This file supplies the stricter alternative promised by the
`UnitCostRAM` documentation.  A program is a finite list of instructions; the
interpreter, rather than the program author, charges every executed
instruction.

The word type is the exact-real unit-cost model: an integer, Boolean, or exact
real occupies one word.  Integer/real arithmetic, comparison, indirect load,
indirect store, and control transfer each cost one local step.  Allocating or
freeing a block of `k` words costs `k + 1` local steps; hence a single bulk
instruction cannot hide exponential working space in a polynomial-time run.
An external
call additionally increments the oracle counter and charges every argument
and answer word transferred.  Likewise, `halt` charges every output word read
from RAM.  Thus a one-instruction bulk transfer cannot hide an exponentially
long answer.  A random-bit instruction increments the randomness counter.
The interpreter is fuelled only to make
its Lean definition total.  A complexity certificate must prove that the
fuelled execution actually halts and bound the cost returned by the
interpreter.

This is a RAM/BSS-style operational semantics, not a Turing-machine encoding.
It complements rather than replaces the higher-level `CostM` API: algorithms
may first be verified compositionally with `CostM`, and particularly sensitive
claims can additionally be compiled to this syntax.

The finite-program/random-access organization follows Cook--Reckhow's RAM
framework; exact-real arithmetic follows Blum--Shub--Smale.  The separation
between local steps, oracle calls, samples, and random bits reflects the
distinct resource measures used in oracle and randomized algorithms rather
than pretending that a continuously distributed real sample is a finite bit
string.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM

universe u v w

noncomputable section

namespace Word

/-- Canonical zero word used for initially empty registers and memory. -/
def zero : Word := .integer 0

/-- Read a nonnegative integer word as a RAM address. -/
def asAddress : Word → Option ℕ
  | .integer value => if 0 ≤ value then some value.toNat else none
  | _ => none

/-- Integer addition is defined only on integer words. -/
def integerAdd : Word → Word → Option Word
  | .integer left, .integer right => some (.integer (left + right))
  | _, _ => none

def integerSub : Word → Word → Option Word
  | .integer left, .integer right => some (.integer (left - right))
  | _, _ => none

def integerMul : Word → Word → Option Word
  | .integer left, .integer right => some (.integer (left * right))
  | _, _ => none

def integerDiv : Word → Word → Option Word
  | .integer left, .integer right =>
      if right = 0 then none else some (.integer (left / right))
  | _, _ => none

def integerMod : Word → Word → Option Word
  | .integer left, .integer right =>
      if right = 0 then none else some (.integer (left % right))
  | _, _ => none

/-- BSS/real-RAM exact real arithmetic. -/
def realAdd : Word → Word → Option Word
  | .real left, .real right => some (.real (left + right))
  | _, _ => none

def realSub : Word → Word → Option Word
  | .real left, .real right => some (.real (left - right))
  | _, _ => none

def realMul : Word → Word → Option Word
  | .real left, .real right => some (.real (left * right))
  | _, _ => none

def realDiv : Word → Word → Option Word
  | .real left, .real right =>
      if right = 0 then none else some (.real (left / right))
  | _, _ => none

def realLE : Word → Word → Option Word
  | .real left, .real right => some (.bit (decide (left ≤ right)))
  | _, _ => none

def integerLE : Word → Word → Option Word
  | .integer left, .integer right => some (.bit (decide (left ≤ right)))
  | _, _ => none

def booleanNot : Word → Option Word
  | .bit value => some (.bit (!value))
  | _ => none

def booleanAnd : Word → Word → Option Word
  | .bit left, .bit right => some (.bit (left && right))
  | _, _ => none

def booleanOr : Word → Word → Option Word
  | .bit left, .bit right => some (.bit (left || right))
  | _, _ => none

end Word

/-- Infinite mathematical register/memory maps.  Only finitely many cells are
reachable in any fuel-bounded execution. -/
abbrev RegisterFile := ℕ → Word
abbrev RAMMemory := ℕ → Word

/-- Read `count` consecutive words. -/
def readWords (memory : RAMMemory) (start count : ℕ) : List Word :=
  List.ofFn fun index : Fin count => memory (start + index)

/-- Write a consecutive list of words. -/
def writeWords : RAMMemory → ℕ → List Word → RAMMemory
  | memory, _, [] => memory
  | memory, address, word :: words =>
      writeWords (Function.update memory address word) (address + 1) words

/-- Load a finite input into memory starting at address zero. -/
def inputMemory (input : List Word) : RAMMemory :=
  fun address => (input[address]?).getD Word.zero

/-- Complete machine configuration. -/
structure MachineState where
  pc : ℕ
  registers : RegisterFile
  memory : RAMMemory
  /-- Number of currently live allocated words. -/
  liveCells : ℕ
  /-- Next fresh address for the simple bump allocator. -/
  nextFresh : ℕ
  /-- Position in the external random-bit tape. -/
  randomCursor : ℕ

/-- Initial state: input words occupy the first memory cells and register `0`
contains the input length. -/
def MachineState.initial (input : List Word) : MachineState where
  pc := 0
  registers := Function.update (fun _ => Word.zero) 0 (.integer input.length)
  memory := inputMemory input
  liveCells := input.length
  nextFresh := input.length
  randomCursor := 0

/-- Instructions of the finite real-RAM program.  Register operands are named
by natural indices.  `call` reads/writes consecutive memory blocks whose
addresses and lengths are stored in registers. -/
inductive Instruction (ExternalOperation : Type u)
  | halt (startRegister lengthRegister : ℕ)
  | constant (destination : ℕ) (value : Word)
  | move (destination source : ℕ)
  | load (destination addressRegister : ℕ)
  | store (addressRegister source : ℕ)
  | integerAdd (destination left right : ℕ)
  | integerSub (destination left right : ℕ)
  | integerMul (destination left right : ℕ)
  | integerDiv (destination left right : ℕ)
  | integerMod (destination left right : ℕ)
  | realAdd (destination left right : ℕ)
  | realSub (destination left right : ℕ)
  | realMul (destination left right : ℕ)
  | realDiv (destination left right : ℕ)
  | integerLE (destination left right : ℕ)
  | realLE (destination left right : ℕ)
  | booleanNot (destination source : ℕ)
  | booleanAnd (destination left right : ℕ)
  | booleanOr (destination left right : ℕ)
  | jump (target : ℕ)
  | branch (conditionRegister ifTrue ifFalse : ℕ)
  | allocate (amountRegister destinationAddressRegister : ℕ)
  | free (amountRegister : ℕ)
  | randomBit (destination : ℕ)
  | call (operation : ExternalOperation)
      (argumentStartRegister argumentLengthRegister : ℕ)
      (resultStartRegister resultLengthDestination : ℕ)
  | sample (operation : ExternalOperation)
      (parameterStartRegister parameterLengthRegister : ℕ)
      (resultStartRegister resultLengthDestination : ℕ)

/-- A finite program.  Falling past the code is a fault, never an implicit
successful halt. -/
structure Program (ExternalOperation : Type u) where
  code : Array (Instruction ExternalOperation)

/-- One plus the greatest register index mentioned by an instruction (with
`1` as the harmless minimum for instructions mentioning no register). -/
def Instruction.registerCount {ExternalOperation : Type u} :
    Instruction ExternalOperation → ℕ
  | .halt start length => max start length + 1
  | .constant destination _ => destination + 1
  | .move destination source => max destination source + 1
  | .load destination address => max destination address + 1
  | .store address source => max address source + 1
  | .integerAdd destination left right
  | .integerSub destination left right
  | .integerMul destination left right
  | .integerDiv destination left right
  | .integerMod destination left right
  | .realAdd destination left right
  | .realSub destination left right
  | .realMul destination left right
  | .realDiv destination left right
  | .integerLE destination left right
  | .realLE destination left right
  | .booleanAnd destination left right
  | .booleanOr destination left right => max destination (max left right) + 1
  | .booleanNot destination source => max destination source + 1
  | .jump _ => 1
  | .branch condition _ _ => condition + 1
  | .allocate amount destination => max amount destination + 1
  | .free amount => amount + 1
  | .randomBit destination => destination + 1
  | .call _ argumentStart argumentLength resultStart resultLength =>
      max argumentStart (max argumentLength (max resultStart resultLength)) + 1
  | .sample _ parameterStart parameterLength resultStart resultLength =>
      max parameterStart (max parameterLength (max resultStart resultLength)) + 1

/-- Static number of registers required by the finite program. -/
def Program.registerCount {ExternalOperation : Type u}
    (program : Program ExternalOperation) : ℕ :=
  program.code.foldl
    (fun current instruction => max current instruction.registerCount) 1

/-- Semantics of explicitly declared external/oracle operations and of the
random tape.  The interpreter charges the call plus argument/answer transfer,
but it does **not** charge evaluation of the arbitrary Lean function
`external`.  Thus this field denotes a unit-cost oracle boundary.  Treating it
as an ordinary local subroutine requires a separately formalized cost contract
and an operational composition theorem. -/
structure MachineEnvironment (ExternalOperation : Type u) where
  external : ExternalOperation → List Word → List Word
  randomTape : ℕ → Bool

inductive StepStatus
  | running
  | halted (output : List Word)
  | faulted

structure StepOutcome where
  state : MachineState
  status : StepStatus

private def advance (state : MachineState) : MachineState :=
  { state with pc := state.pc + 1 }

private def writeRegister (state : MachineState) (register : ℕ)
    (value : Word) : MachineState :=
  { state with
    pc := state.pc + 1
    registers := Function.update state.registers register value }

private def binaryRegisterOperation (state : MachineState)
    (destination left right : ℕ)
    (operation : Word → Word → Option Word) : StepOutcome :=
  match operation (state.registers left) (state.registers right) with
  | some value => ⟨writeRegister state destination value, .running⟩
  | none => ⟨state, .faulted⟩

private def localOutcome (outcome : StepOutcome) : ProfiledCost StepOutcome :=
  ⟨outcome, (ResourceCounts.localStep, 0)⟩

private def fault (state : MachineState) : ProfiledCost StepOutcome :=
  localOutcome ⟨state, .faulted⟩

/-- Execute exactly one fetched instruction.  Type/address errors produce a
charged fault. -/
def executeInstruction {ExternalOperation : Type u}
    (environment : MachineEnvironment ExternalOperation)
    (state : MachineState) (instruction : Instruction ExternalOperation) :
    ProfiledCost StepOutcome :=
  match instruction with
  | .halt startRegister lengthRegister =>
      match (state.registers startRegister).asAddress,
          (state.registers lengthRegister).asAddress with
      | some start, some length =>
          if start + length ≤ state.nextFresh then
            ⟨⟨state, .halted (readWords state.memory start length)⟩,
              (ResourceCounts.localSteps (length + 1), 0)⟩
          else fault state
      | _, _ => fault state
  | .constant destination value =>
      localOutcome ⟨writeRegister state destination value, .running⟩
  | .move destination source =>
      localOutcome
        ⟨writeRegister state destination (state.registers source), .running⟩
  | .load destination addressRegister =>
      match (state.registers addressRegister).asAddress with
      | some address =>
          if address < state.nextFresh then
            localOutcome
              ⟨writeRegister state destination (state.memory address), .running⟩
          else fault state
      | none => fault state
  | .store addressRegister source =>
      match (state.registers addressRegister).asAddress with
      | some address =>
          if address < state.nextFresh then
            localOutcome
              ⟨advance { state with
                  memory := Function.update state.memory address
                    (state.registers source) }, .running⟩
          else fault state
      | none => fault state
  | .integerAdd destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerAdd)
  | .integerSub destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerSub)
  | .integerMul destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerMul)
  | .integerDiv destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerDiv)
  | .integerMod destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerMod)
  | .realAdd destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realAdd)
  | .realSub destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realSub)
  | .realMul destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realMul)
  | .realDiv destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realDiv)
  | .integerLE destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerLE)
  | .realLE destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realLE)
  | .booleanNot destination source =>
      match Word.booleanNot (state.registers source) with
      | some value =>
          localOutcome ⟨writeRegister state destination value, .running⟩
      | none => fault state
  | .booleanAnd destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.booleanAnd)
  | .booleanOr destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.booleanOr)
  | .jump target => localOutcome ⟨{ state with pc := target }, .running⟩
  | .branch conditionRegister ifTrue ifFalse =>
      match state.registers conditionRegister with
      | .bit condition =>
          localOutcome
            ⟨{ state with pc := if condition then ifTrue else ifFalse }, .running⟩
      | _ => fault state
  | .allocate amountRegister destinationAddressRegister =>
      match (state.registers amountRegister).asAddress with
      | some amount =>
          let start := state.nextFresh
          let nextState :=
            writeRegister
              { state with
                liveCells := state.liveCells + amount
                nextFresh := state.nextFresh + amount }
              destinationAddressRegister (.integer start)
          ⟨⟨nextState, .running⟩,
            (ResourceCounts.localSteps (amount + 1), Cells.alloc amount)⟩
      | none => fault state
  | .free amountRegister =>
      match (state.registers amountRegister).asAddress with
      | some amount =>
          if amount ≤ state.liveCells then
            ⟨⟨advance { state with
                  liveCells := state.liveCells - amount
                  nextFresh := state.nextFresh - amount },
                .running⟩,
              (ResourceCounts.localSteps (amount + 1), Cells.free amount)⟩
          else fault state
      | none => fault state
  | .randomBit destination =>
      let bit := environment.randomTape state.randomCursor
      let nextState := writeRegister
        { state with randomCursor := state.randomCursor + 1 }
        destination (.bit bit)
      ⟨⟨nextState, .running⟩,
        (ResourceCounts.randomness 1, 0)⟩
  | .call operation argumentStartRegister argumentLengthRegister
      resultStartRegister resultLengthDestination =>
      match (state.registers argumentStartRegister).asAddress,
          (state.registers argumentLengthRegister).asAddress,
          (state.registers resultStartRegister).asAddress with
      | some argumentStart, some argumentLength, some resultStart =>
          let answer := environment.external operation
            (readWords state.memory argumentStart argumentLength)
          if argumentStart + argumentLength ≤ state.nextFresh ∧
              resultStart + answer.length ≤ state.nextFresh then
            let nextState := writeRegister
              { state with memory := writeWords state.memory resultStart answer }
              resultLengthDestination (.integer answer.length)
            ⟨⟨nextState, .running⟩,
              (ResourceCounts.oracleQueryTransfer
                argumentLength answer.length, 0)⟩
          else fault state
      | _, _, _ => fault state
  | .sample operation parameterStartRegister parameterLengthRegister
      resultStartRegister resultLengthDestination =>
      match (state.registers parameterStartRegister).asAddress,
          (state.registers parameterLengthRegister).asAddress,
          (state.registers resultStartRegister).asAddress with
      | some parameterStart, some parameterLength, some resultStart =>
          let answer := environment.external operation
            (readWords state.memory parameterStart parameterLength)
          if parameterStart + parameterLength ≤ state.nextFresh ∧
              resultStart + answer.length ≤ state.nextFresh then
            let nextState := writeRegister
              { state with memory := writeWords state.memory resultStart answer }
              resultLengthDestination (.integer answer.length)
            ⟨⟨nextState, .running⟩,
              (ResourceCounts.distributionSampleTransfer
                parameterLength answer.length, 0)⟩
          else fault state
      | _, _, _ => fault state

/-- Fetch and execute one instruction. -/
def step {ExternalOperation : Type u}
    (environment : MachineEnvironment ExternalOperation)
    (program : Program ExternalOperation) (state : MachineState) :
    ProfiledCost StepOutcome :=
  match program.code[state.pc]? with
  | some instruction => executeInstruction environment state instruction
  | none => fault state

inductive ExecutionResult
  | halted (output : List Word) (state : MachineState)
  | faulted (state : MachineState)
  | outOfFuel (state : MachineState)

/-- Fuelled reflexive execution.  All actual resource counts come from
`step`; fuel exhaustion itself adds no fictitious machine instruction. -/
def execute {ExternalOperation : Type u}
    (environment : MachineEnvironment ExternalOperation)
    (program : Program ExternalOperation) : ℕ → MachineState →
      ProfiledCost ExecutionResult
  | 0, state => ⟨.outOfFuel state, 0⟩
  | fuel + 1, state =>
      let one := step environment program state
      match one.ret.status with
      | .running =>
          let rest := execute environment program fuel one.ret.state
          ⟨rest.ret, one.cost + rest.cost⟩
      | .halted output => ⟨.halted output one.ret.state, one.cost⟩
      | .faulted => ⟨.faulted one.ret.state, one.cost⟩

/-- Run a program from its canonical input state. -/
def run {ExternalOperation : Type u}
    (environment : MachineEnvironment ExternalOperation)
    (program : Program ExternalOperation) (fuel : ℕ)
    (input : List Word) : ProfiledCost ExecutionResult :=
  execute environment program fuel (MachineState.initial input)

/-- Environment for a program with no external operations and a fixed random
tape. -/
def closedEnvironment (randomTape : ℕ → Bool) :
    MachineEnvironment Empty where
  external operation := nomatch operation
  randomTape := randomTape

/-- Lossless output representation for an execution whose output type depends
on both the ordinary input and an auxiliary seed/oracle/adversarial choice. -/
structure ChoiceDependentEncoding
    {Input : Type u} {Choice : Input → Type v}
    (Output : (input : Input) → Choice input → Type w) where
  encode : (input : Input) → (choice : Choice input) →
    Output input choice → List Word
  decode : (input : Input) → (choice : Choice input) →
    List Word → Option (Output input choice)
  decode_encode : ∀ input choice output,
    decode input choice (encode input choice output) = some output


/-!
## Fixed-representation polynomial-time certificates

The encodings in this section are parameters, not fields chosen by the
implementation witness.  This follows the design of mathlib's
`Turing.TM2ComputableInPolyTime`, used in OpenAI's `ten-proofs`: the
representation is fixed before the finite program is exhibited, the time
majorant is an explicit polynomial, and the bound is imposed on the actual
interpreter trace.  Fixing the encodings prevents a purported implementation
from hiding the mathematical computation in a witness-specific decoder.

The API is deliberately split into two layers.  A
`FixedEncodingRAMImplementation` first identifies the exact execution and its
operation-count function.  The separate predicate
`FixedEncodingRAMImplementation.IsPolynomialTime` then asks for constants
`c, k : ℕ` giving the bound `c * (inputSize + 1)^k`.
`StrictRAMComputableInPolyTime` below bundles both layers for concise use in
problem statements.
-/

/-- Step 1: a finite closed RAM program computing a mathematical function
with fixed input/output representations.  This structure records the exact
execution to be counted but makes no asymptotic claim. -/
structure FixedEncodingRAMImplementation
    {Input : Type u} {Output : Input → Type v}
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (function : (input : Input) → Output input) where
  program : Program Empty
  fuel : Input → ℕ
  correct : ∀ input,
    ∃ finalState,
      (run (closedEnvironment fun _ ↦ false) program (fuel input)
          (inputEncoding.encode input)).ret =
        .halted (outputEncoding.encode input (function input)) finalState

namespace FixedEncodingRAMImplementation

variable {Input : Type u} {Output : Input → Type v}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {function : (input : Input) → Output input}

/-- The instruction-enforced execution whose cost is used by every later
resource predicate. -/
def execution
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function)
    (input : Input) : ProfiledCost ExecutionResult :=
  run (closedEnvironment fun _ ↦ false) implementation.program
    (implementation.fuel input) (inputEncoding.encode input)

/-- Step 1 output: the exact number of local RAM steps charged by the
interpreter on one input. -/
def operationCount
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function)
    (input : Input) : ℕ :=
  ProfiledCost.steps (implementation.execution input)

/-- Complete exact resource record generated by the interpreter on one
input.  This is the canonical output of the counting stage, before any
polynomial majorant is chosen. -/
def resourceUsage
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function)
    (input : Input) : ProfiledCost.ExactResourceUsage :=
  ProfiledCost.exactResourceUsage (implementation.execution input)

/-- Exact value of one standard resource on one input. -/
def standardResourceCount
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function)
    (resource : ProfiledCost.StandardResource)
    (input : Input) : ℕ :=
  (implementation.resourceUsage input).get resource


/-- Step 2: the counted execution has a natural-coefficient polynomial
majorant in the length of the fixed input encoding. -/
def IsPolynomialTime
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function) : Prop :=
  IsPolyBound inputEncoding.size implementation.operationCount

/-- Generic step-2 predicate for any natural-valued statistic extracted from
the same execution.  It covers time, oracle calls, samples, random bits,
communication, output delay, and space without introducing a new complexity
definition for each resource. -/
def HasPolynomialResource
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function)
    (resource : Input → ProfiledCost ExecutionResult → ℕ) : Prop :=
  IsPolyBound inputEncoding.size fun input =>
    resource input (implementation.execution input)

/-- Step 2 for a named standard resource.  Unlike `HasPolynomialResource`,
this predicate cannot choose an arbitrary execution inspector: it bounds one
of the counters fixed by the operational semantics. -/
def HasPolynomialStandardResource
    (implementation : FixedEncodingRAMImplementation
      inputEncoding outputEncoding function)
    (resource : ProfiledCost.StandardResource) : Prop :=
  IsPolyBound inputEncoding.size fun input =>
    implementation.standardResourceCount resource input


end FixedEncodingRAMImplementation

/-- A finite closed real-RAM program computing `function` in time bounded by
an explicit natural-coefficient polynomial in a *fixed* lossless input
encoding.  The dependent output encoding is also fixed outside the witness.

The same interpreter execution appears in both `correct` and `time_bound`, so
the polynomial certificate cannot count a cheaper execution than the one that
produces the advertised output.  Correctness requires the machine to emit the
canonical word list supplied by the fixed output encoding.  Merely emitting
some alias accepted by `decode` is intentionally insufficient: otherwise a
decoder could perform hidden computation, and independently certified
programs could not be composed by passing their raw outputs. -/
structure StrictRAMComputableInPolyTime
    {Input : Type u} {Output : Input → Type v}
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (function : (input : Input) → Output input) where
  program : Program Empty
  fuel : Input → ℕ
  coefficient : ℕ
  exponent : ℕ
  correct : ∀ input,
    ∃ finalState,
      (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)).ret =
        .halted (outputEncoding.encode input (function input)) finalState
  time_bound : ∀ input,
    ProfiledCost.steps
        (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)) ≤
      coefficient * (inputEncoding.size input + 1) ^ exponent

namespace StrictRAMComputableInPolyTime

variable {Input : Type u} {Output : Input → Type v}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {function : (input : Input) → Output input}

/-- Forget only the polynomial certificate while retaining the exact program,
canonical correctness statement, and execution to be counted. -/
def toImplementation
    (certificate : StrictRAMComputableInPolyTime
      inputEncoding outputEncoding function) :
    FixedEncodingRAMImplementation inputEncoding outputEncoding function where
  program := certificate.program
  fuel := certificate.fuel
  correct := certificate.correct


end StrictRAMComputableInPolyTime


/-- Step 1 for randomized, oracle, sampling, and adversarial executions: the
external-operation type, environment, and encodings are fixed outside the
implementation, while one finite program must work for every choice. -/
structure FixedEnvironmentRAMImplementation
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (inputEncoding : Encoding Input)
    (outputEncoding : ChoiceDependentEncoding Output)
    (ExternalOperation : Type*)
    (environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation)
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) where
  choice_nonempty : ∀ input, Nonempty (Choice input)
  program : Program ExternalOperation
  fuel : (input : Input) → Choice input → ℕ
  correct : ∀ input choice,
    ∃ finalState,
      (run (environment input choice) program (fuel input choice)
          (inputEncoding.encode input)).ret =
        .halted
          (outputEncoding.encode input choice (function input choice))
          finalState

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

def execution
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function)
    (input : Input) (choice : Choice input) : ProfiledCost ExecutionResult :=
  run (environment input choice) implementation.program
    (implementation.fuel input choice) (inputEncoding.encode input)

/-- Exact step count of one selected execution. -/
def operationCount
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function)
    (input : Input) (choice : Choice input) : ℕ :=
  ProfiledCost.steps (implementation.execution input choice)

/-- Complete exact resource record for one selected legal environment
execution.  Uniform bounds below quantify over every `choice`, but the
counting operation itself is a plain executable projection of this run. -/
def resourceUsage
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function)
    (input : Input) (choice : Choice input) :
    ProfiledCost.ExactResourceUsage :=
  ProfiledCost.exactResourceUsage (implementation.execution input choice)

/-- Exact value of one named standard resource for a selected execution. -/
def standardResourceCount
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function)
    (resource : ProfiledCost.StandardResource)
    (input : Input) (choice : Choice input) : ℕ :=
  (implementation.resourceUsage input choice).get resource


/-- Step 2 requires one polynomial uniformly over every legal execution
choice. -/
def IsPolynomialTime
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function) : Prop :=
  IsUniformPolyBound inputEncoding.size implementation.operationCount

/-- Uniform polynomial bound for an arbitrary statistic of the exact chosen
execution. -/
def HasPolynomialResource
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function)
    (resource : (input : Input) → Choice input →
      ProfiledCost ExecutionResult → ℕ) : Prop :=
  IsUniformPolyBound inputEncoding.size fun input choice =>
    resource input choice (implementation.execution input choice)

/-- Uniform polynomial bound for one standard interpreter-generated
resource.  This is the preferred generic resource predicate for
problem-facing statements. -/
def HasPolynomialStandardResource
    (implementation : FixedEnvironmentRAMImplementation inputEncoding
      outputEncoding ExternalOperation environment function)
    (resource : ProfiledCost.StandardResource) : Prop :=
  IsUniformPolyBound inputEncoding.size fun input choice =>
    implementation.standardResourceCount resource input choice


end FixedEnvironmentRAMImplementation

/-- Preferred choice/oracle certificate with the external-operation type and
semantics fixed by the surrounding problem statement.  Keeping `environment`
outside the witness prevents a purported implementation from installing an
ad-hoc oracle that simply returns the desired mathematical answer.

An external operation is an explicit oracle boundary.  The interpreter
charges the call/sample instruction and records its resource counter, but does
not charge the Lean computation used to implement `environment.external`.
Consequently a theorem using this structure must either interpret external
operations as unit-cost oracle queries, or separately supply and compose a
running-time contract for their implementation. -/
structure StrictRAMComputableInPolyTimeWithFixedEnvironment
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (inputEncoding : Encoding Input)
    (outputEncoding : ChoiceDependentEncoding Output)
    (ExternalOperation : Type*)
    (environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation)
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) where
  choice_nonempty : ∀ input, Nonempty (Choice input)
  program : Program ExternalOperation
  fuel : (input : Input) → Choice input → ℕ
  coefficient : ℕ
  exponent : ℕ
  correct : ∀ input choice,
    ∃ finalState,
      (run (environment input choice) program (fuel input choice)
          (inputEncoding.encode input)).ret =
        .halted
          (outputEncoding.encode input choice (function input choice))
          finalState
  time_bound : ∀ input choice,
    ProfiledCost.steps
        (run (environment input choice) program (fuel input choice)
          (inputEncoding.encode input)) ≤
      coefficient * (inputEncoding.size input + 1) ^ exponent

/-- Step-1 implementation for a promise search problem.  The interpreter
chooses an encoded solution, while `correct` connects that exact output to the
search relation on valid inputs. -/
structure FixedEncodingRAMSearchImplementation
    {Input : Type u} {Output : Input → Type v}
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (valid : Input → Prop)
    (solution : (input : Input) → Output input → Prop) where
  program : Program Empty
  fuel : Input → ℕ
  correct : ∀ input, valid input →
    ∃ output finalState,
      (run (closedEnvironment fun _ ↦ false) program (fuel input)
          (inputEncoding.encode input)).ret =
        .halted (outputEncoding.encode input output) finalState ∧
      solution input output

namespace FixedEncodingRAMSearchImplementation

variable {Input : Type u} {Output : Input → Type v}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {valid : Input → Prop}
  {solution : (input : Input) → Output input → Prop}

def execution
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution)
    (input : Input) : ProfiledCost ExecutionResult :=
  run (closedEnvironment fun _ ↦ false) implementation.program
    (implementation.fuel input) (inputEncoding.encode input)

def operationCount
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution)
    (input : Input) : ℕ :=
  ProfiledCost.steps (implementation.execution input)

/-- Complete exact resource record for one promise-search execution. -/
def resourceUsage
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution)
    (input : Input) : ProfiledCost.ExactResourceUsage :=
  ProfiledCost.exactResourceUsage (implementation.execution input)

/-- Exact value of one standard resource on one search instance. -/
def standardResourceCount
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution)
    (resource : ProfiledCost.StandardResource)
    (input : Input) : ℕ :=
  (implementation.resourceUsage input).get resource


/-- Step 2 only constrains instances in the promise domain. -/
def IsPolynomialTimeOn
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution) : Prop :=
  IsPolyBoundOn valid inputEncoding.size implementation.operationCount

def HasPolynomialResourceOn
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution)
    (resource : Input → ProfiledCost ExecutionResult → ℕ) : Prop :=
  IsPolyBoundOn valid inputEncoding.size fun input =>
    resource input (implementation.execution input)

/-- Promise-restricted polynomial bound for one named standard resource. -/
def HasPolynomialStandardResourceOn
    (implementation : FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution)
    (resource : ProfiledCost.StandardResource) : Prop :=
  IsPolyBoundOn valid inputEncoding.size fun input =>
    implementation.standardResourceCount resource input


end FixedEncodingRAMSearchImplementation

/-- A fixed-representation polynomial-time solver for a dependent search
relation on a promise domain.  Unlike `CostedSearchImplementation`, both the
answer and its running time come from the same finite instruction-level
execution.  Correctness may select any valid mathematical output, but the raw
machine result must be its canonical fixed encoding.  No canonical choice
*among solutions* is built into the statement. -/
structure StrictRAMSearchableInPolyTime
    {Input : Type u} {Output : Input → Type v}
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (valid : Input → Prop)
    (solution : (input : Input) → Output input → Prop) where
  program : Program Empty
  fuel : Input → ℕ
  coefficient : ℕ
  exponent : ℕ
  correct : ∀ input, valid input →
    ∃ output finalState,
      (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)).ret =
        .halted (outputEncoding.encode input output) finalState ∧
      solution input output
  time_bound : ∀ input, valid input →
    ProfiledCost.steps
        (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)) ≤
      coefficient * (inputEncoding.size input + 1) ^ exponent

namespace StrictRAMSearchableInPolyTime

variable {Input : Type u} {Output : Input → Type v}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {valid : Input → Prop}
  {solution : (input : Input) → Output input → Prop}

def toImplementation
    (certificate : StrictRAMSearchableInPolyTime
      inputEncoding outputEncoding valid solution) :
    FixedEncodingRAMSearchImplementation
      inputEncoding outputEncoding valid solution where
  program := certificate.program
  fuel := certificate.fuel
  correct := certificate.correct


end StrictRAMSearchableInPolyTime


namespace StrictRAMComputableInPolyTimeWithFixedEnvironment

def toImplementation
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
    FixedEnvironmentRAMImplementation inputEncoding outputEncoding
      ExternalOperation environment function where
  choice_nonempty := certificate.choice_nonempty
  program := certificate.program
  fuel := certificate.fuel
  correct := certificate.correct


def execution
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
      inputEncoding outputEncoding ExternalOperation environment function)
    (input : Input) (choice : Choice input) : ProfiledCost ExecutionResult :=
  run (environment input choice) certificate.program
    (certificate.fuel input choice) (inputEncoding.encode input)

def HasPolynomialQueries
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
      inputEncoding outputEncoding ExternalOperation environment function) : Prop :=
  IsUniformPolyBound inputEncoding.size fun input choice =>
    ProfiledCost.oracleQueries (certificate.execution input choice)

def UsesPolynomialRandomBits
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
      inputEncoding outputEncoding ExternalOperation environment function) : Prop :=
  IsUniformPolyBound inputEncoding.size fun input choice =>
    ProfiledCost.randomBits (certificate.execution input choice)

def UsesPolynomialSamples
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
      inputEncoding outputEncoding ExternalOperation environment function) : Prop :=
  IsUniformPolyBound inputEncoding.size fun input choice =>
    ProfiledCost.distributionSamples (certificate.execution input choice)

def UsesPolynomialSpace
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
      inputEncoding outputEncoding ExternalOperation environment function) : Prop :=
  IsUniformPolyBound inputEncoding.size fun input choice =>
    certificate.program.registerCount + inputEncoding.size input +
      ProfiledCost.peakCells (certificate.execution input choice)

end StrictRAMComputableInPolyTimeWithFixedEnvironment

end

end EconCSLib.OpenProblem.UnitCostRAM

