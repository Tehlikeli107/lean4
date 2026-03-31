/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Internal.Order.Basic
import all Init.System.ST  -- for EST.bind in MonoBindRight instance

set_option linter.missingDocs true

public section

namespace Lean.Order

/--
The class `MonoBindRight m` indicates that every `m α` has a `CCPO`, and that the bind operation
on `m` is monotone in the second argument with regard to that order.

This is a weaker requirement than `MonoBind`, which requires monotonicity in both arguments.
`MonoBindRight` is sufficient for `partial_fixpoint`-based recursive definitions where the
recursive call only appears in the continuation (second argument) of `>>=`.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used
otherwise.
-/
class MonoBindRight (m : Type u → Type v) [Bind m] where
  /-- Every `m β` with `Nonempty β` has a chain-complete partial order. -/
  instCCPO β [Nonempty β] : CCPO (m β)
  /-- Bind is monotone in the second (continuation) argument. -/
  bind_mono_right {a : m α} {f₁ f₂ : α → m β} [Nonempty β] (h : ∀ x, f₁ x ⊑ f₂ x) :
    a >>= f₁ ⊑ a >>= f₂

attribute [implicit_reducible] MonoBindRight.instCCPO
attribute [instance] MonoBindRight.instCCPO

/-- Monotonicity lemma for bind when the recursive call is in the continuation. -/
@[partial_fixpoint_monotone]
theorem MonoBindRight.monotone_bind_right
    (m : Type u → Type v) [Monad m] [MonoBindRight m]
    {α β : Type u} [Nonempty β]
    {γ : Sort w} [PartialOrder γ]
    (f : m α) (g : γ → α → m β)
    (hmono : monotone g) :
    monotone (fun (x : γ) => f >>= g x) :=
  fun _ _ h => MonoBindRight.bind_mono_right (hmono _ _ h)

instance : MonoBindRight Id where
  instCCPO _ := inferInstanceAs (CCPO (FlatOrder (b := Classical.ofNonempty)))
  bind_mono_right h := h _

instance {σ : Type u} {m : Type u → Type v} [Monad m] [MonoBindRight m] [Nonempty σ] :
    MonoBindRight (StateT σ m) where
  instCCPO α := inferInstanceAs (CCPO (σ → m (α × σ)))
  bind_mono_right h := by
    intro s
    show StateT.bind _ _ s ⊑ StateT.bind _ _ s
    simp only [StateT.bind]
    apply MonoBindRight.bind_mono_right (m := m)
    intro ⟨x, s'⟩
    exact h x s'

instance {ε : Type u} {m : Type u → Type v} [Monad m] [MonoBindRight m] :
    MonoBindRight (ExceptT ε m) where
  instCCPO β := MonoBindRight.instCCPO (Except ε β)
  bind_mono_right h := by
    apply MonoBindRight.bind_mono_right (m := m)
    intro x
    cases x with
    | error => exact PartialOrder.rel_refl
    | ok a => exact h a

instance : MonoBindRight (Except ε) where
  instCCPO β := inferInstanceAs (CCPO (FlatOrder (b := Classical.ofNonempty)))
  bind_mono_right h := by
    cases ‹Except _ _› with
    | error => exact FlatOrder.rel.refl
    | ok a => exact h a

instance {m : Type u → Type v} [Monad m] [MonoBindRight m] :
    MonoBindRight (OptionT m) where
  instCCPO β := MonoBindRight.instCCPO (Option β)
  bind_mono_right h := by
    apply MonoBindRight.bind_mono_right (m := m)
    intro x
    cases x with
    | none => exact PartialOrder.rel_refl
    | some a => exact h a

instance : MonoBindRight Option where
  instCCPO _ := inferInstance
  bind_mono_right h := MonoBind.bind_mono_right h

instance {ρ : Type u} {m : Type u → Type v} [Monad m] [MonoBindRight m] :
    MonoBindRight (ReaderT ρ m) where
  instCCPO α := inferInstanceAs (CCPO (ρ → m α))
  bind_mono_right h := by
    intro r
    show ReaderT.bind _ _ r ⊑ ReaderT.bind _ _ r
    simp only [ReaderT.bind]
    apply MonoBindRight.bind_mono_right (m := m)
    intro x
    exact h x r

set_option linter.missingDocs false in
noncomputable def ST.bot' [Nonempty α] (s : Void σ) : @FlatOrder (ST.Out σ α) (.mk Classical.ofNonempty (Classical.choice ⟨s⟩)) :=
  .mk Classical.ofNonempty (Classical.choice ⟨s⟩)

instance [Nonempty α] : CCPO (ST σ α) where
  rel := PartialOrder.rel (α := ∀ s, FlatOrder (ST.bot' s))
  rel_refl := PartialOrder.rel_refl
  rel_antisymm := PartialOrder.rel_antisymm
  rel_trans := PartialOrder.rel_trans
  has_csup hchain := CCPO.has_csup (α := ∀ s, FlatOrder (ST.bot' s)) hchain

instance : MonoBindRight (ST σ) where
  instCCPO _ := inferInstance
  bind_mono_right {_ _ a f₁ f₂} _ h := by
    intro w
    change FlatOrder.rel (ST.bind a f₁ w) (ST.bind a f₂ w)
    simp only [ST.bind]
    apply h

instance : MonoBindRight BaseIO :=
  inferInstanceAs (MonoBindRight (ST IO.RealWorld))

instance [Nonempty ε] : MonoBindRight (EST ε σ) where
  instCCPO _ := inferInstance
  bind_mono_right h := MonoBind.bind_mono_right h

instance [Nonempty ε] : MonoBindRight (EIO ε) :=
  inferInstanceAs (MonoBindRight (EST ε IO.RealWorld))

instance : MonoBindRight IO :=
  inferInstanceAs (MonoBindRight (EIO IO.Error))

instance {ω : Type} {σ : Type} {m : Type → Type} [Monad m] [MonoBindRight m] :
    MonoBindRight (StateRefT' ω σ m) :=
  inferInstanceAs (MonoBindRight (ReaderT (ST.Ref ω σ) m))

end Lean.Order
