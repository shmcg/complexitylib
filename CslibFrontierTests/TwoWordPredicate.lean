/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordPredicate

/-! # Native predicates on two stored words and their physical input tape -/

namespace CslibFrontierTests.TwoWordPredicate

open Turing Turing.MultiTapeTM Turing.MultiTapeATM

-- Both answers use one fixed machine. Arbitrary first words include the empty-word boundary,
-- where serialization must still emit the framing delimiter before the second component.
example : ∃ (K : ℕ) (i j : Fin K) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM K Bool Q) (c : ℕ), i ≠ j ∧ ∀ input word : List Bool,
      let yes := (TwoWordInput.ready i j input word [true]).withState
        (some atm.toPTM.initial)
      let no := (TwoWordInput.ready i j input word [false]).withState
        (some atm.toPTM.initial)
      let time := c * (4 * word.length + 5)
      atm.HaltsWithin time yes ∧ atm.HaltsWithin time no ∧
        atm.AcceptsWithin time yes ∧ ¬atm.AcceptsWithin time no := by
  have hp : ComputableInO (Prod.snd : List Bool × Bool → Bool)
      (encPair encBits encBool) encBool
      (fun p => (encPair encBits encBool p).length)
      (fun p => (encPair encBits encBool p).length) :=
    .of_linear (PairEncoding.snd (enc₁ := encBits) (enc₂ := encBool))
  obtain ⟨K, i, j, Q, hQ, atm, c, hij, h⟩ := TwoWordPredicate.exists_of_inO hp
  refine ⟨K, i, j, Q, hQ, atm, c, hij, ?_⟩
  intro input word
  have ht (b : Bool) : (encPair encBits encBool (word, b)).length +
      (encPair encBits encBool (word, b)).length + 1 = 4 * word.length + 5 := by
    simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton]
    omega
  have hy := h input word true
  have hn := h input word false
  simp only [encBits_apply, encBool_apply, ht] at hy hn
  exact ⟨hy.1, hn.1, hy.2.mpr trivial, fun ha => Bool.false_ne_true (hn.2.mp ha)⟩

-- Identical stored words give opposite answers when only the physical host bit changes.
-- Arbitrary stored words include both empty fields in the same finite-machine witness.
example : ∃ (K : ℕ) (i j : Fin K) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM K Bool Q) (C : ℕ), i ≠ j ∧ ∀ first second : List Bool,
      let start := fun bit : Bool => (TwoWordInput.ready i j [bit] first second).withState
        (some atm.toPTM.initial)
      let time := C * (3 * first.length + 2 * second.length + 6)
      atm.HaltsWithin time (start true) ∧ atm.HaltsWithin time (start false) ∧
        atm.AcceptsWithin time (start true) ∧ ¬ atm.AcceptsWithin time (start false) := by
  let enc := encPair encBool (encPair encBits encBits)
  have hp : ComputableInO (Prod.fst : Bool × List Bool × List Bool → Bool) enc encBool
      (fun p => (enc p).length) (fun p => (enc p).length) :=
    .of_linear (PairEncoding.fst (enc₁ := encBool) (enc₂ := encPair encBits encBits))
  obtain ⟨K, i, j, Q, hQ, atm, C, hij, h⟩ := TwoWordPredicate.exists_of_host_inO hp
  refine ⟨K, i, j, Q, hQ, atm, C, hij, ?_⟩
  intro first second start time
  have ht (b : Bool) : (encBool b).length + (encBits first).length + (encBits second).length +
      (enc (b, first, second)).length + 1 = 3 * first.length + 2 * second.length + 6 := by
    simp only [enc, length_encPair, encBits_apply, encBool_apply, List.length_singleton]
    omega
  have answer (b : Bool) : atm.HaltsWithin time (start b) ∧
      (atm.AcceptsWithin time (start b) ↔ b = true) := by
    have hb := h b first second
    dsimp only at hb
    rw [ht] at hb
    exact hb
  exact ⟨(answer true).1, (answer false).1, (answer true).2.mpr rfl,
    fun ha => Bool.false_ne_true ((answer false).2.mp ha)⟩

end CslibFrontierTests.TwoWordPredicate
