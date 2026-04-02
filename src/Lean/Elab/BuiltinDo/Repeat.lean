/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.BuiltinDo.Basic
meta import Lean.Parser.Do
import Lean.Elab.BuiltinDo.For
import Lean.Elab.Do.Switch

public section

namespace Lean.Elab.Do

open Lean.Parser.Term

@[builtin_doElem_elab Lean.doRepeat] def elabDoRepeat : DoElab := fun stx dec => do
  let `(doElem| repeat $seq) := stx | throwUnsupportedSyntax
  let expanded ←
    if Term.backward.do.while.get (← getOptions) then
      `(doElem| for _ in Loop.mk do $seq)
    else
      `(doElem| for _ in Repeat.mk do $seq)
  Term.withMacroExpansion stx expanded <|
    withRef expanded <| elabDoElem ⟨expanded⟩ dec

end Lean.Elab.Do
