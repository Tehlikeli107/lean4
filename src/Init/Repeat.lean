/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Core
public import Init.Internal.Order.MonadTail
import Init.While

set_option linter.missingDocs true

@[expose] public section

namespace Lean

open Lean.Order

/-!
# `Repeat` type for verified `repeat`/`while` loops

This module provides a `Repeat` type that serves as an alternative to `Loop` for `repeat`/`while`
loops. Unlike `Loop`, which uses `partial` recursion, `Repeat` is implemented using
`partial_fixpoint` and `MonadTail`, enabling verified reasoning about loop programs.
-/

/-- A type for `repeat`/`while` loops that supports verified reasoning via `partial_fixpoint`. -/
structure Repeat where

set_option linter.missingDocs false in
open Lean.Order.MonadTail in
def Repeat.forIn {β : Type u} {m : Type u → Type v}
    [Nonempty β] [Monad m] [Lean.Order.MonadTail m]
    (b : β) (f : Unit → β → m (ForInStep β)) : m β := do
  match ← f () b with
  | ForInStep.done b => pure b
  | ForInStep.yield b => Repeat.forIn b f
partial_fixpoint

instance [Monad m] [Lean.Order.MonadTail m] : ForIn m Repeat Unit where
  forIn _ init f := haveI : Nonempty _ := ⟨init⟩; Repeat.forIn init f

macro_rules
  | `(doElem| repeat $seq) => do
    if ← Macro.hasDecl `Lean.Elab.Do.elabDoRepeat then
      Lean.Macro.throwUnsupported
    `(doElem| for _ in Repeat.mk do $seq)

end Lean
