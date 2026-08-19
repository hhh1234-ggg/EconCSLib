/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity.Definitions.UnitCostRAM
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Support library for unit-cost RAM accounting

This module supplies named proof lemmas, traversal combinators, closure rules,
parallel-accounting helpers, and legacy trusted instrumentation interfaces on
top of the foundational definitions in `Complexity.Definitions.UnitCostRAM`.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM

open scoped BigOperators

universe u v w

/-! ## Basic cost equations and traversal helpers -/

namespace Cost

variable {α : Type u} {β : Type v} {γ : Type w}

@[simp] theorem value_pure (a : α) : (pure a).value = a := rfl
@[simp] theorem ops_pure (a : α) : (pure a).ops = 0 := rfl
@[simp] theorem value_bind (x : Cost α) (f : α → Cost β) :
    (bind x f).value = (f x.value).value := rfl
@[simp] theorem ops_bind (x : Cost α) (f : α → Cost β) :
    (bind x f).ops = x.ops + (f x.value).ops := rfl
@[simp] theorem value_map (f : α → β) (x : Cost α) :
    (map f x).value = f x.value := rfl
@[simp] theorem ops_map (f : α → β) (x : Cost α) :
    (map f x).ops = x.ops := rfl

@[simp] theorem ops_tick (x : Cost α) : (tick x).ops = x.ops + 1 := rfl
@[simp] theorem ops_liftUnary (op : α → β) (x : Cost α) :
    (liftUnary op x).ops = x.ops + 1 := rfl
@[simp] theorem ops_liftBinary (op : α → β → γ) (x : Cost α) (y : Cost β) :
    (liftBinary op x y).ops = x.ops + y.ops + 1 := rfl
@[simp] theorem ops_liftTernary {δ : Type*} (op : α → β → γ → δ)
    (x : Cost α) (y : Cost β) (z : Cost γ) :
    (liftTernary op x y z).ops = x.ops + y.ops + z.ops + 1 := rfl

/-- Sum over a finite collection, charging each body and one visit per item. -/
def sumFinset {ι : Type*} [AddCommMonoid α]
    (s : Finset ι) (f : ι → Cost α) : Cost α :=
  ⟨∑ i ∈ s, (f i).value, (∑ i ∈ s, (f i).ops) + s.card⟩

@[simp] theorem value_sumFinset {ι : Type*} [AddCommMonoid α]
    (s : Finset ι) (f : ι → Cost α) :
    (sumFinset s f).value = ∑ i ∈ s, (f i).value := rfl

@[simp] theorem ops_sumFinset {ι : Type*} [AddCommMonoid α]
    (s : Finset ι) (f : ι → Cost α) :
    (sumFinset s f).ops = (∑ i ∈ s, (f i).ops) + s.card := rfl

/-- Product counterpart of `sumFinset`. -/
def prodFinset {ι : Type*} [CommMonoid α]
    (s : Finset ι) (f : ι → Cost α) : Cost α :=
  ⟨∏ i ∈ s, (f i).value, (∑ i ∈ s, (f i).ops) + s.card⟩

@[simp] theorem value_prodFinset {ι : Type*} [CommMonoid α]
    (s : Finset ι) (f : ι → Cost α) :
    (prodFinset s f).value = ∏ i ∈ s, (f i).value := rfl

@[simp] theorem ops_prodFinset {ι : Type*} [CommMonoid α]
    (s : Finset ι) (f : ι → Cost α) :
    (prodFinset s f).ops = (∑ i ∈ s, (f i).ops) + s.card := rfl

/-- Filter a finite collection, charging the predicate and one visit per item. -/
def filterFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Cost Bool) : Cost (Finset ι) :=
  ⟨s.filter (fun i => (p i).value), (∑ i ∈ s, (p i).ops) + s.card⟩

@[simp] theorem ops_filterFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Cost Bool) :
    (filterFinset s p).ops = (∑ i ∈ s, (p i).ops) + s.card := rfl

/-- Stateful left fold. Each iteration charges its body and loop control. -/
def foldlList (step : β → α → Cost β) : List α → β → Cost β
  | [], state => pure state
  | item :: items, state =>
      let next := step state item
      let tail := foldlList step items next.value
      ⟨tail.value, next.ops + tail.ops + 1⟩

/-- Map a costed computation over a list with one control step per item. -/
def mapList (f : α → Cost β) : List α → Cost (List β)
  | [] => pure []
  | item :: items =>
      let head := f item
      let tail := mapList f items
      ⟨head.value :: tail.value, head.ops + tail.ops + 1⟩

/-- Execute a state transition exactly `iterations` times. -/
def iterate (iterations : ℕ) (step : α → Cost α) (initial : α) : Cost α :=
  match iterations with
  | 0 => pure initial
  | n + 1 =>
      let next := step initial
      let tail := iterate n step next.value
      ⟨tail.value, next.ops + tail.ops + 1⟩

/-- Result of a fuel-bounded while loop. -/
inductive WhileResult (α : Type u)
  | done (state : α)
  | exhausted (state : α)

/-- Total semantics for a fuel-bounded while loop. -/
def whileFuel (fuel : ℕ) (condition : α → Cost Bool)
    (body : α → Cost α) (initial : α) : Cost (WhileResult α) :=
  match fuel with
  | 0 => pure (.exhausted initial)
  | n + 1 =>
      let test := condition initial
      if test.value then
        let next := body initial
        let tail := whileFuel n condition body next.value
        ⟨tail.value, test.ops + next.ops + tail.ops + 1⟩
      else
        ⟨.done initial, test.ops + 1⟩

@[simp] theorem ops_foldlList_nil (step : β → α → Cost β) (state : β) :
    (foldlList step [] state).ops = 0 := rfl

@[simp] theorem ops_foldlList_cons (step : β → α → Cost β)
    (item : α) (items : List α) (state : β) :
    (foldlList step (item :: items) state).ops =
      (step state item).ops +
        (foldlList step items (step state item).value).ops + 1 := rfl

@[simp] theorem ops_mapList (f : α → Cost β) (items : List α) :
    (mapList f items).ops =
      (items.map fun item => (f item).ops).sum + items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      change (f item).ops + (mapList f items).ops + 1 =
        (f item).ops + (items.map fun x => (f x).ops).sum +
          (items.length + 1)
      rw [ih]
      omega

theorem ops_iterate_le (iterations bodyBound : ℕ) (step : α → Cost α)
    (initial : α) (hstep : ∀ state, (step state).ops ≤ bodyBound) :
    (iterate iterations step initial).ops ≤ iterations * (bodyBound + 1) := by
  induction iterations generalizing initial with
  | zero => simp [iterate, ops, pure, CostM.pure]
  | succ n ih =>
      simp only [iterate]
      calc
        (step initial).ops + (iterate n step (step initial).value).ops + 1
            ≤ bodyBound + n * (bodyBound + 1) + 1 := by
                exact Nat.add_le_add_right
                  (Nat.add_le_add (hstep initial) (ih (step initial).value)) 1
        _ = (n + 1) * (bodyBound + 1) := by ring

theorem ops_foldlList_le (step : β → α → Cost β) (items : List α)
    (initial : β) (bodyBound : ℕ)
    (hstep : ∀ state item, (step state item).ops ≤ bodyBound) :
    (foldlList step items initial).ops ≤
      items.length * (bodyBound + 1) := by
  induction items generalizing initial with
  | nil =>
      simp only [ops_foldlList_nil, List.length_nil, Nat.zero_mul]
      exact le_rfl
  | cons item items ih =>
      rw [ops_foldlList_cons]
      calc
        (step initial item).ops +
              (foldlList step items (step initial item).value).ops + 1
            ≤ bodyBound + items.length * (bodyBound + 1) + 1 := by
                exact Nat.add_le_add_right
                  (Nat.add_le_add (hstep initial item)
                    (ih (step initial item).value)) 1
        _ = (item :: items).length * (bodyBound + 1) := by
          simp only [List.length_cons]
          ring

theorem ops_whileFuel_le (fuel conditionBound bodyBound : ℕ)
    (condition : α → Cost Bool) (body : α → Cost α) (initial : α)
    (hcondition : ∀ state, (condition state).ops ≤ conditionBound)
    (hbody : ∀ state, (body state).ops ≤ bodyBound) :
    (whileFuel fuel condition body initial).ops ≤
      fuel * (conditionBound + bodyBound + 1) := by
  induction fuel generalizing initial with
  | zero =>
      simp only [whileFuel, ops_pure, Nat.zero_mul]
      exact le_rfl
  | succ remaining ih =>
      simp only [whileFuel]
      split
      · have htest := hcondition initial
        have hnext := hbody initial
        have hrest := ih (body initial).value
        calc
          (condition initial).ops + (body initial).ops +
                (whileFuel remaining condition body
                  (body initial).value).ops + 1
              ≤ conditionBound + bodyBound +
                    remaining * (conditionBound + bodyBound + 1) + 1 := by
                  omega
          _ = (remaining + 1) * (conditionBound + bodyBound + 1) := by ring
      · have htest := hcondition initial
        have hbase : conditionBound + 1 ≤
            conditionBound + bodyBound + 1 := by omega
        calc
          (condition initial).ops + 1 ≤ conditionBound + 1 := by omega
          _ ≤ conditionBound + bodyBound + 1 := hbase
          _ ≤ (remaining + 1) *
                (conditionBound + bodyBound + 1) := by
              exact Nat.le_mul_of_pos_left _ (Nat.succ_pos remaining)

end Cost

/-! ## Encoding equations -/

theorem Encoding.encode_injective {Input : Type u}
    (encoding : Encoding Input) : Function.Injective encoding.encode := by
  intro left right h
  apply Option.some.inj
  calc
    some left = encoding.decode (encoding.encode left) :=
      (encoding.decode_encode left).symm
    _ = encoding.decode (encoding.encode right) := congrArg encoding.decode h
    _ = some right := encoding.decode_encode right

namespace Encoding

@[simp] theorem size_dependent {Index : Type v} {Value : Type u}
    (encoding : Encoding Value) (index : Index) (value : Value) :
    (encoding.dependent.size index value) = encoding.size value := rfl

@[simp] theorem size_sigma {Input : Type u} {Output : Input → Type v}
    (input : Encoding Input) (output : DependentEncoding Output)
    (pair : Σ i, Output i) :
    (input.sigma output).size pair =
      input.size pair.1 + output.size pair.1 pair.2 + 1 := by
  simp [Encoding.size, sigma, DependentEncoding.size]

end Encoding

/-! ## Exact-resource equations -/

namespace ResourceCounts

@[simp] theorem steps_zero : (0 : ResourceCounts).steps = 0 := rfl
@[simp] theorem queries_zero : (0 : ResourceCounts).oracleQueries = 0 := rfl
@[simp] theorem samples_zero : (0 : ResourceCounts).distributionSamples = 0 := rfl
@[simp] theorem randomBits_zero : (0 : ResourceCounts).randomBits = 0 := rfl
@[simp] theorem communicationUnits_zero :
    (0 : ResourceCounts).communicationUnits = 0 := rfl

@[simp] theorem steps_add (left right : ResourceCounts) :
    (left + right).steps = left.steps + right.steps := rfl
@[simp] theorem queries_add (left right : ResourceCounts) :
    (left + right).oracleQueries =
      left.oracleQueries + right.oracleQueries := rfl
@[simp] theorem samples_add (left right : ResourceCounts) :
    (left + right).distributionSamples =
      left.distributionSamples + right.distributionSamples := rfl
@[simp] theorem randomBits_add (left right : ResourceCounts) :
    (left + right).randomBits = left.randomBits + right.randomBits := rfl
@[simp] theorem communicationUnits_add (left right : ResourceCounts) :
    (left + right).communicationUnits =
      left.communicationUnits + right.communicationUnits := rfl

end ResourceCounts

namespace ProfiledCost

variable {α : Type u}

@[simp] theorem exactResourceUsage_localSteps (run : ProfiledCost α) :
    (exactResourceUsage run).localSteps = steps run := rfl

@[simp] theorem exactResourceUsage_oracleQueries (run : ProfiledCost α) :
    (exactResourceUsage run).oracleQueries = oracleQueries run := rfl

@[simp] theorem exactResourceUsage_distributionSamples
    (run : ProfiledCost α) :
    (exactResourceUsage run).distributionSamples =
      distributionSamples run := rfl

@[simp] theorem exactResourceUsage_randomBits (run : ProfiledCost α) :
    (exactResourceUsage run).randomBits = randomBits run := rfl

@[simp] theorem exactResourceUsage_communicationUnits
    (run : ProfiledCost α) :
    (exactResourceUsage run).communicationUnits =
      communicationUnits run := rfl

@[simp] theorem exactResourceUsage_peakAuxiliaryCells
    (run : ProfiledCost α) :
    (exactResourceUsage run).peakAuxiliaryCells = peakCells run := rfl

@[simp] theorem oracleQueries_oracleCall {Query Answer : Type*}
    (oracle : Query → Answer) (query : ProfiledCost Query) :
    oracleQueries (oracleCall oracle query) = oracleQueries query + 1 := rfl

@[simp] theorem distributionSamples_sampleCall {Parameter Sample : Type*}
    (sampler : Parameter → Sample) (parameter : ProfiledCost Parameter) :
    distributionSamples (sampleCall sampler parameter) =
      distributionSamples parameter + 1 := rfl

@[simp] theorem communicatedBits_send (message : List Bool) :
    communicatedBits (send message) = message.length := rfl

@[simp] theorem communicationUnits_sendWords (message : List Word) :
    communicationUnits (sendWords message) = message.length := rfl

@[simp] theorem randomBits_consumeRandomBits (bits : List Bool) :
    randomBits (consumeRandomBits bits) = bits.length := rfl

@[simp] theorem peakCells_alloc (cells : ℕ) :
    peakCells (alloc cells) = cells := by simp [peakCells, alloc, charge]

end ProfiledCost

/-! ## Parallel work and span -/

/-- Work/span pair for fork-join parallel algorithms. -/
@[ext]
structure WorkSpan where
  work : ℕ
  span : ℕ
  deriving DecidableEq

namespace WorkSpan

instance : Zero WorkSpan := ⟨⟨0, 0⟩⟩
instance : Add WorkSpan :=
  ⟨fun left right =>
    ⟨left.work + right.work, left.span + right.span⟩⟩
instance : AddCommMonoid WorkSpan where
  add_assoc _ _ _ := by ext <;> exact Nat.add_assoc _ _ _
  zero_add _ := by ext <;> exact Nat.zero_add _
  add_zero _ := by ext <;> exact Nat.add_zero _
  add_comm _ _ := by ext <;> exact Nat.add_comm _ _
  nsmul := nsmulRec

/-- Combine independent computations in parallel. -/
def parallel {α : Type u} {β : Type v}
    (left : CostM WorkSpan α) (right : CostM WorkSpan β) :
    CostM WorkSpan (α × β) :=
  ⟨(left.ret, right.ret),
    ⟨left.cost.work + right.cost.work,
      max left.cost.span right.cost.span⟩⟩

end WorkSpan

/-! ## Polynomial closure rules -/

namespace IsPolyBound

variable {Input : Type u} {sizeOf : Input → ℕ}

theorem const (n : ℕ) : IsPolyBound sizeOf (fun _ => n) :=
  ⟨n, 0, fun _ => by simp⟩

theorem self : IsPolyBound sizeOf sizeOf :=
  ⟨1, 1, fun input => by simp⟩

theorem of_le {f g : Input → ℕ} (hg : IsPolyBound sizeOf g)
    (hfg : ∀ input, f input ≤ g input) : IsPolyBound sizeOf f := by
  obtain ⟨c, k, hg⟩ := hg
  exact ⟨c, k, fun input => (hfg input).trans (hg input)⟩

theorem add {f g : Input → ℕ} (hf : IsPolyBound sizeOf f)
    (hg : IsPolyBound sizeOf g) :
    IsPolyBound sizeOf (fun input => f input + g input) := by
  obtain ⟨cf, kf, hf⟩ := hf
  obtain ⟨cg, kg, hg⟩ := hg
  refine ⟨cf + cg, max kf kg, fun input => ?_⟩
  have hbase : 1 ≤ sizeOf input + 1 := by omega
  have hpowf :
      (sizeOf input + 1) ^ kf ≤ (sizeOf input + 1) ^ max kf kg :=
    Nat.pow_le_pow_right hbase (le_max_left _ _)
  have hpowg :
      (sizeOf input + 1) ^ kg ≤ (sizeOf input + 1) ^ max kf kg :=
    Nat.pow_le_pow_right hbase (le_max_right _ _)
  calc
    f input + g input
        ≤ cf * (sizeOf input + 1) ^ kf +
            cg * (sizeOf input + 1) ^ kg := Nat.add_le_add (hf input) (hg input)
    _ ≤ cf * (sizeOf input + 1) ^ max kf kg +
          cg * (sizeOf input + 1) ^ max kf kg := by gcongr
    _ = (cf + cg) * (sizeOf input + 1) ^ max kf kg := by ring

theorem mul {f g : Input → ℕ} (hf : IsPolyBound sizeOf f)
    (hg : IsPolyBound sizeOf g) :
    IsPolyBound sizeOf (fun input => f input * g input) := by
  obtain ⟨cf, kf, hf⟩ := hf
  obtain ⟨cg, kg, hg⟩ := hg
  refine ⟨cf * cg, kf + kg, fun input => ?_⟩
  calc
    f input * g input
        ≤ (cf * (sizeOf input + 1) ^ kf) *
            (cg * (sizeOf input + 1) ^ kg) := Nat.mul_le_mul (hf input) (hg input)
    _ = cf * cg * (sizeOf input + 1) ^ (kf + kg) := by
      rw [pow_add]
      ring

end IsPolyBound

/-! ## Loop-composition rules -/

theorem isPolyTime_sumFinset
    {Input Index Value : Type*} [AddCommMonoid Value]
    {sizeOf : Input → ℕ} {indices : Input → Finset Index}
    {body : (input : Input) → Index → Cost Value}
    {bodyBound : Input → ℕ}
    (hcard : IsPolyBound sizeOf (fun input => (indices input).card))
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hbody : ∀ input index, index ∈ indices input →
      (body input index).ops ≤ bodyBound input) :
    IsPolyTime sizeOf
      (fun input => Cost.sumFinset (indices input) (body input)) := by
  show IsPolyBound sizeOf
    (fun input => (Cost.sumFinset (indices input) (body input)).ops)
  have htotal : IsPolyBound sizeOf
      (fun input => (indices input).card * (bodyBound input + 1)) :=
    IsPolyBound.mul hcard
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1))
  refine IsPolyBound.of_le htotal (fun input => ?_)
  have hsum :
      (∑ index ∈ indices input, (body input index).ops) ≤
        ∑ _index ∈ indices input, bodyBound input :=
    Finset.sum_le_sum (fun index hindex => hbody input index hindex)
  calc
    (Cost.sumFinset (indices input) (body input)).ops
        = (∑ index ∈ indices input, (body input index).ops) +
            (indices input).card := rfl
    _ ≤ (∑ _index ∈ indices input, bodyBound input) +
          (indices input).card := Nat.add_le_add_right hsum _
    _ = (indices input).card * bodyBound input +
          (indices input).card := by
      rw [Finset.sum_const]
      simp
    _ = (indices input).card * (bodyBound input + 1) := by ring

theorem isPolyTime_filterFinset
    {Input Index : Type*} [DecidableEq Index]
    {sizeOf : Input → ℕ} {indices : Input → Finset Index}
    {predicate : (input : Input) → Index → Cost Bool}
    {predicateBound : Input → ℕ}
    (hcard : IsPolyBound sizeOf (fun input => (indices input).card))
    (hpredicateBound : IsPolyBound sizeOf predicateBound)
    (hpredicate : ∀ input index, index ∈ indices input →
      (predicate input index).ops ≤ predicateBound input) :
    IsPolyTime sizeOf
      (fun input => Cost.filterFinset (indices input) (predicate input)) := by
  show IsPolyBound sizeOf
    (fun input =>
      (Cost.filterFinset (indices input) (predicate input)).ops)
  have htotal : IsPolyBound sizeOf
      (fun input => (indices input).card * (predicateBound input + 1)) :=
    IsPolyBound.mul hcard
      (IsPolyBound.add hpredicateBound (IsPolyBound.const 1))
  refine IsPolyBound.of_le htotal (fun input => ?_)
  have hsum :
      (∑ index ∈ indices input, (predicate input index).ops) ≤
        ∑ _index ∈ indices input, predicateBound input :=
    Finset.sum_le_sum
      (fun index hindex => hpredicate input index hindex)
  calc
    (Cost.filterFinset (indices input) (predicate input)).ops
        = (∑ index ∈ indices input, (predicate input index).ops) +
            (indices input).card := rfl
    _ ≤ (∑ _index ∈ indices input, predicateBound input) +
          (indices input).card := Nat.add_le_add_right hsum _
    _ = (indices input).card * predicateBound input +
          (indices input).card := by
      rw [Finset.sum_const]
      simp
    _ = (indices input).card * (predicateBound input + 1) := by ring

theorem isPolyTime_foldlList
    {Input Item State : Type*}
    {sizeOf : Input → ℕ} {items : Input → List Item}
    {initial : Input → State}
    {step : (input : Input) → State → Item → Cost State}
    {bodyBound : Input → ℕ}
    (hlength : IsPolyBound sizeOf (fun input => (items input).length))
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hstep : ∀ input state item,
      (step input state item).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input =>
      Cost.foldlList (step input) (items input) (initial input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.foldlList (step input) (items input) (initial input)).ops
  apply IsPolyBound.of_le
    (IsPolyBound.mul hlength
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1)))
  intro input
  exact Cost.ops_foldlList_le _ _ _ _ (hstep input)

theorem isPolyTime_mapList
    {Input Item Value : Type*}
    {sizeOf : Input → ℕ} {items : Input → List Item}
    {body : (input : Input) → Item → Cost Value}
    {bodyBound : Input → ℕ}
    (hlength : IsPolyBound sizeOf (fun input => (items input).length))
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hbody : ∀ input item, (body input item).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input => Cost.mapList (body input) (items input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.mapList (body input) (items input)).ops
  apply IsPolyBound.of_le
    (IsPolyBound.mul hlength
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1)))
  intro input
  rw [Cost.ops_mapList]
  have hsum :
      ((items input).map fun item => (body input item).ops).sum ≤
        (items input).length * bodyBound input := by
    calc
      ((items input).map fun item => (body input item).ops).sum
          ≤ ((items input).map fun _ => bodyBound input).sum := by
              exact List.sum_le_sum fun item _ => hbody input item
      _ = (items input).length * bodyBound input := by simp
  calc
    ((items input).map fun item => (body input item).ops).sum +
          (items input).length
        ≤ (items input).length * bodyBound input +
            (items input).length := Nat.add_le_add_right hsum _
    _ = (items input).length * (bodyBound input + 1) := by ring

theorem isPolyTime_iterate
    {Input State : Type*} {sizeOf : Input → ℕ}
    {iterations bodyBound : Input → ℕ}
    {step : (input : Input) → State → Cost State}
    {initial : Input → State}
    (hiterations : IsPolyBound sizeOf iterations)
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hstep : ∀ input state, (step input state).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input =>
      Cost.iterate (iterations input) (step input) (initial input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.iterate (iterations input) (step input) (initial input)).ops
  apply IsPolyBound.of_le
    (IsPolyBound.mul hiterations
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1)))
  intro input
  exact Cost.ops_iterate_le _ _ _ _ (hstep input)

theorem isPolyTime_dependentIterate
    {Input : Type u} {State : Input → Type v} {sizeOf : Input → ℕ}
    {iterations bodyBound : Input → ℕ}
    {step : (input : Input) → State input → Cost (State input)}
    {initial : (input : Input) → State input}
    (hiterations : IsPolyBound sizeOf iterations)
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hstep : ∀ input state, (step input state).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input =>
      Cost.iterate (iterations input) (step input) (initial input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.iterate (iterations input) (step input) (initial input)).ops
  apply IsPolyBound.of_le
    (IsPolyBound.mul hiterations
      (IsPolyBound.add hbodyBound (IsPolyBound.const 1)))
  intro input
  exact Cost.ops_iterate_le _ _ _ _ (hstep input)

theorem isPolyTime_whileFuel
    {Input State : Type*} {sizeOf : Input → ℕ}
    {fuel conditionBound bodyBound : Input → ℕ}
    {condition : (input : Input) → State → Cost Bool}
    {body : (input : Input) → State → Cost State}
    {initial : Input → State}
    (hfuel : IsPolyBound sizeOf fuel)
    (hconditionBound : IsPolyBound sizeOf conditionBound)
    (hbodyBound : IsPolyBound sizeOf bodyBound)
    (hcondition : ∀ input state,
      (condition input state).ops ≤ conditionBound input)
    (hbody : ∀ input state,
      (body input state).ops ≤ bodyBound input) :
    IsPolyTime sizeOf fun input =>
      Cost.whileFuel (fuel input) (condition input) (body input)
        (initial input) := by
  show IsPolyBound sizeOf fun input =>
    (Cost.whileFuel (fuel input) (condition input) (body input)
      (initial input)).ops
  have hperIteration : IsPolyBound sizeOf fun input =>
      conditionBound input + bodyBound input + 1 :=
    IsPolyBound.add (IsPolyBound.add hconditionBound hbodyBound)
      (IsPolyBound.const 1)
  apply IsPolyBound.of_le (IsPolyBound.mul hfuel hperIteration)
  intro input
  exact Cost.ops_whileFuel_le _ _ _ _ _ _
    (hcondition input) (hbody input)

end EconCSLib.OpenProblem.UnitCostRAM
