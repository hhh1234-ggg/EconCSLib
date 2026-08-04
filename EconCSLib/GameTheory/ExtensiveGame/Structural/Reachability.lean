/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Structural.Basic

/-!
# Payoff-free reachability

Finite transition reachability for `Arena`, together with reachability from a
`ControlledGame` root. The relation records existence of a path; it makes no
finiteness, acyclicity, or decidability assumption.

## Main definitions

* `Arena.Reachable` — finite transition reachability between Arena states.
* `ControlledGame.IsReachable` — reachability from a controlled game's root.
-/

namespace Arena

/-- A state `t` is reachable from `s` if a finite legal path leads from `s` to
`t`. -/
inductive Reachable (A : Arena) : A.State → A.State → Prop where
  | refl (s : A.State) : A.Reachable s s
  | step {s t : A.State} (a : A.Action s)
      (h : A.Reachable (A.next s a) t) :
      A.Reachable s t

namespace Reachable

/-- Reachability is transitive. -/
theorem trans {A : Arena} {s t u : A.State}
    (h₁ : A.Reachable s t) (h₂ : A.Reachable t u) :
    A.Reachable s u := by
  induction h₁ with
  | refl => exact h₂
  | step action _ ih => exact .step action (ih h₂)

/-- Taking one legal action extends a reachable path. -/
theorem step' {A : Arena} {s t : A.State}
    (h : A.Reachable s t) (action : A.Action t) :
    A.Reachable s (A.next t action) :=
  h.trans (.step action (.refl _))

end Reachable

end Arena

namespace ControlledGame

variable {N : Type*}

/-- A state is reachable in a controlled game if it is reachable from its
distinguished initial state. -/
def IsReachable (G : ControlledGame N) (state : G.State) : Prop :=
  G.toArena.Reachable G.init state

/-- The initial state is reachable. -/
theorem isReachable_init (G : ControlledGame N) : G.IsReachable G.init :=
  .refl _

/-- A legal successor of a reachable state is reachable. -/
theorem IsReachable.next {G : ControlledGame N} {state : G.State}
    (h : G.IsReachable state) (action : G.Action state) :
    G.IsReachable (G.next state action) :=
  h.step' action

end ControlledGame
