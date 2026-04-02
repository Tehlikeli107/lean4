/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.Triple.SpecLemmas
import Std.Tactic.Do.Syntax

set_option linter.missingDocs true

@[expose] public section

namespace Std.Do

/-!
# Specification theorem for `Repeat` loops

This file contains the `@[spec]` theorem for `forIn` over `Lean.Repeat`, which enables
verified reasoning about `repeat`/`while` loops using `mvcgen`.
-/

set_option mvcgen.warning false

/-- A variant (termination measure) for a `Repeat`/`while` loop. -/
@[spec_invariant_type]
abbrev RepeatVariant (β : Type u) (ps : PostShape.{u}) := β → SVal ps.args (ULift Nat)

set_option linter.missingDocs false in
abbrev RepeatVariant.eval {β ps} (variant : RepeatVariant β ps) (b : β) (n : Nat) :=
  SPred.evalsTo (variant b) ⟨n⟩

/-- An invariant for a `Repeat`/`while` loop. -/
@[spec_invariant_type]
abbrev RepeatInvariant β ps := PostCond (Bool × β) ps

section

variable {β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}

private theorem RepeatVariant.eval_total {P : SPred ps.args} (variant : RepeatVariant β ps) (b : β) :
    P ⊢ₛ ∃ m, RepeatVariant.eval variant b m := by
  mintro _
  mhave h2 := SPred.evalsTo_total (variant b)
  mcases h2 with ⟨m, h2⟩
  mexists m.down

private theorem RepeatVariant.add_eval {P Q : SPred ps.args} (variant : RepeatVariant β ps) (b : β)
    (h : spred(∃ m, RepeatVariant.eval variant b m ∧ P) ⊢ₛ Q) : P ⊢ₛ Q := by
  apply SPred.entails.trans _ h
  mintro _
  mhave h2 := RepeatVariant.eval_total variant b
  mcases h2 with ⟨m, h2⟩
  mexists m
  mconstructor <;> massumption

end

section

variable {β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
variable [Monad m] [Lean.Order.MonadTail m] [WPMonad m ps]

@[spec]
theorem Spec.forIn_repeat
    {l : _root_.Lean.Repeat} {init : β} {f : Unit → β → m (ForInStep β)}
    (measure : RepeatVariant β ps)
    (inv : RepeatInvariant β ps)
    (step : ∀ b mb,
      Triple (f () b)
        spred(RepeatVariant.eval measure b mb ∧ inv.1 (false, b))
        (fun r => match r with
          | .yield b' => spred(∃ mb', RepeatVariant.eval measure b' mb' ∧ ⌜mb' < mb⌝ ∧ inv.1 (false, b'))
          | .done b' => inv.1 (true, b'), inv.2)) :
    Triple (forIn l init f) spred(inv.1 (false, init)) (fun b => inv.1 (true, b), inv.2) := by
  haveI : Nonempty β := ⟨init⟩
  simp only [forIn]
  apply RepeatVariant.add_eval measure init
  apply SPred.exists_elim
  intro minit
  induction minit using Nat.strongRecOn generalizing init with
  | _ minit ih =>
  rw [_root_.Lean.Repeat.forIn.eq_1]
  mvcgen [step, ih] with
  | vc2 =>
    mrename_i h
    mcases h with ⟨mb', ⟨hmeasure, ⌜hmb'⌝, h⟩⟩
    mspec Triple.of_entails_wp (ih mb' hmb')

end

end Std.Do
