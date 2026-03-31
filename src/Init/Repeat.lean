/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Core
public import Init.Internal.Order.MonoBindRight
import Init.While

set_option linter.missingDocs true

@[expose] public section

namespace Lean

open Lean.Order

/-!
# Well-founded `Repeat` type for verified `repeat`/`while` loops

This module provides a `Repeat` type that serves as an alternative to `Loop` for `repeat`/`while`
loops. Unlike `Loop`, which uses `partial` recursion, `Repeat` is implemented using
`partial_fixpoint` and `MonoBindRight`, enabling verified reasoning about loop programs.
-/

/-- A type for `repeat`/`while` loops that supports verified reasoning via `partial_fixpoint`. -/
inductive Repeat where
  /-- Creates a `Repeat` value. -/
  | mk

/-- Iterates the body `f` using `partial_fixpoint` recursion via `MonoBindRight`. -/
def Repeat.forIn {β : Type u} {m : Type u → Type v}
    [Nonempty β] [Monad m] [Lean.Order.MonoBindRight m]
    (b : β) (f : Unit → β → m (ForInStep β)) : m β := do
  match ← f () b with
  | ForInStep.done b => pure b
  | ForInStep.yield b => Repeat.forIn b f
partial_fixpoint

instance [Monad m] [Lean.Order.MonoBindRight m] : ForIn m Repeat Unit where
  forIn _ init f := haveI : Nonempty _ := ⟨init⟩; Repeat.forIn init f

/-- Override the bootstrapping `repeat` macro from `Init.While` to use `Repeat.mk` instead of
`Loop.mk`. When the builtin do-element elaborator for `repeat` is available (`backward.do.while`
option dispatch), this macro defers to it by throwing `unsupportedSyntax`. -/
macro_rules
  | `(doElem| repeat $seq) => do
    if ← Macro.hasDecl `Lean.Elab.Do.elabDoRepeat then
      Lean.Macro.throwUnsupported
    `(doElem| for _ in Repeat.mk do $seq)

end Lean
