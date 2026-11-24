/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordLoad

/-!
# Starting with a source input and a protected challenge

A framed challenge followed by the source word is the sole external input. The loader puts
the challenge at its chosen work-tape origin, exposes only the source through the continuation's
read-only input head, and starts that head on its left blank. The two extra input-simulation
tapes preserve every later move of the alternating continuation. A request already on a
work tape can supply both words through native computations, at any valid head position.
-/

public section

namespace Turing.MultiTapeATM.SourceWordInput

open MultiTapeTM TwoWordLoad

private def locate (k : ℕ) : MultiTapeTM (k + 2) Bool Bool :=
  ofTr false fun phase _ _ =>
    if phase then ⟨0, fun i => if i = Fin.natAdd k 1 then (some (some true), 0) else (none, 0),
      none, none⟩
    else ⟨1, Fin.append (fun _ => (none, 0)) (fun _ : Fin 2 => (none, -1)), none, some true⟩

private theorem locate_spec {K : ℕ} (i : Fin K) (host challenge input : List Bool) :
    let start := TwoWordInput.ready (i.castAdd 2) (Fin.natAdd K 0) host challenge input
    let child := WordGameLeaf.config i (none : Option Bool) challenge 0 (blank K input)
    (locate K).runFrom (start.withState (some (locate K).q₀)) 2 = inCfg true child host := by
  intro start child
  change (locate K).step ((locate K).step (start.withState (some false))) = _
  rw [step_of_state (show (start.withState (some false)).state = some false from rfl)]
  rw [step_of_state (q := true) (by simp [locate, Action.apply])]
  simp only [locate, tr_ofTr, Bool.false_eq_true, ↓reduceIte, start]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [TwoWordInput.ready, Cfg.withState, Action.apply, moveInputPos]
  · funext j z
    cases j using Fin.addCases with
    | left j =>
      by_cases hj : j = i
      · subst j
        simp [child, TwoWordInput.ready, TwoWordInput.words, blank, Cfg.withState, wordsCfg,
          WordGameLeaf.config, Action.apply, Fin.castAdd_ne_natAdd]
      · simp [child, TwoWordInput.ready, TwoWordInput.words, blank, Cfg.withState, wordsCfg,
          WordGameLeaf.config, Action.apply, Fin.castAdd_ne_natAdd, hj, tapesCfg]
    | right j =>
      match j with
      | 0 | 1 =>
        simp [child, TwoWordInput.ready, TwoWordInput.words, Cfg.withState, wordsCfg,
          WordGameLeaf.config, Action.apply, (Fin.castAdd_ne_natAdd _ _).symm, inCfg,
          Function.update]
  · funext j
    cases j using Fin.addCases with
    | left j =>
      simp [child, TwoWordInput.ready, Cfg.withState, wordsCfg, blank, tapesCfg, inCfg,
        WordGameLeaf.config, Action.apply, Fin.castAdd_ne_natAdd]
    | right j =>
      match j with
      | 0 | 1 =>
        simp [child, TwoWordInput.ready, Cfg.withState, wordsCfg, blank, tapesCfg, inCfg,
          WordGameLeaf.config, Action.apply]

private theorem locate_child {K : ℕ} {S : Type} (i : Fin K) (child : MultiTapeATM K Bool S)
    (host request payload : List Bool) (t : ℕ) :
    let load := prependTM (locate K) child.inputFromTape
    let raw := TwoWordInput.ready (i.castAdd 2) (Fin.natAdd K 0) host request payload
    let start := SharedWordFork.start i child payload request 0
    child.HaltsWithin t start →
      load.HaltsWithin (2 + t) (raw.withState (some load.toPTM.initial)) ∧
        (load.AcceptsWithin (2 + t) (raw.withState (some load.toPTM.initial)) ↔
          child.AcceptsWithin t start) := by
  intro load raw start hh
  let storage := inCfg true (WordGameLeaf.config i (none : Option Unit) request 0
    (blank K payload)) host
  have hr : (locate K).runFrom (raw.withState (some (locate K).q₀)) 2 =
      storage.withState none := locate_spec i host request payload
  have ht := (child.haltsWithin_inCfg_iff true host t start).2 hh
  obtain ⟨hl, ha⟩ := prependTM_spec (locate K) child.inputFromTape raw storage 2 t hr ht
  exact ⟨hl, ha.trans (child.acceptsWithin_inCfg_iff true host t start)⟩

/-- Launch a one-word work-tape continuation with its original source as its virtual read-only
input. Splitting the external pair is linear and all subsequent clocks are preserved exactly. -/
theorem exists_prepend {K : ℕ} {S α : Type} [Finite S] (enc : α ↪ List Bool)
    (i : Fin K) (child : MultiTapeATM K Bool S) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C : ℕ),
      ∀ (challenge : α) (input : List Bool) (t : ℕ),
        let pair := encPair enc encBits (challenge, input)
        let start := SharedWordFork.start i child input (enc challenge) 0
        let time := C * (input.length + (enc challenge).length + 1) + t
        child.HaltsWithin t start →
          atm.HaltsWithin time (atm.toPTM.toNTM.initCfg pair) ∧
            (atm.AcceptsWithin time (atm.toPTM.toNTM.initCfg pair) ↔
              child.AcceptsWithin t start) := by
  let load := prependTM (locate K) child.inputFromTape
  obtain ⟨u, Q, hQ, atm, c, hp⟩ := TwoWordInput.exists_prepend enc encBits
    (i.castAdd 2) (Fin.natAdd K 0) (Fin.castAdd_ne_natAdd _ _) load
  refine ⟨u, Q, hQ, atm, 2 * c + 3, ?_⟩
  intro ch input t pair start time hh
  obtain ⟨hl, ha⟩ := locate_child i child pair (enc ch) input t hh
  obtain ⟨he, hv⟩ := hp (ch, input) (2 + t) hl
  have hb : c * (pair.length + 1) + 1 + (2 + t) ≤ time := by
    dsimp only [time, pair]
    rw [length_encPair, encBits_apply, Nat.add_mul]
    nlinarith
  exact ⟨he.mono hb, ⟨fun h => ha.mp (hv.mp (h.of_halted_stepCoins he)),
    fun h => (hv.mpr (ha.mpr h)).mono hb⟩⟩

/-- From a stored request, compute the child's challenge and virtual read-only input. The
head rewind is charged at its actual position and each branch pays the child's clock once. -/
theorem exists_prepend_work {K : ℕ} {S α β : Type} [Finite S] {encIn : α ↪ List Bool}
    {encRequest : β ↪ List Bool} {request : α → β} {payload : α → List Bool} {T : α → ℕ}
    (hr : ComputableInO request encIn encRequest T T) (hp : ComputableInO payload encIn encBits T T)
    (i : Fin K) (child : MultiTapeATM K Bool S) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C : ℕ),
      ∀ (host : List Bool) (a : α) (pos : ℕ), pos ≤ (encIn a).length → ∀ (t : ℕ),
        let target := SharedWordFork.start i child (payload a) (encRequest (request a)) 0
        let start := SharedWordFork.start src atm host (encIn a) pos
        let time := pos + C * (T a + 1) + 10 + t
        child.HaltsWithin t target →
          atm.HaltsWithin time start ∧
            (atm.AcceptsWithin time start ↔ child.AcceptsWithin t target) := by
  let load := prependTM (locate K) child.inputFromTape
  obtain ⟨U, src, Q, hQ, atm, C, h⟩ := TwoWordLoad.exists_load_from hr hp
    (i.castAdd 2) (Fin.natAdd K 0) (Fin.castAdd_ne_natAdd _ _) load
  refine ⟨U, src, Q, hQ, atm, C, ?_⟩
  intro host a pos hpos t target start time hh
  obtain ⟨hl, ha⟩ := locate_child i child host (encRequest (request a)) (payload a) t hh
  obtain ⟨he, hv⟩ := h host a pos hpos (2 + t) hl
  have ht : pos + C * (T a + 1) + 8 + (2 + t) = time := by dsimp only [time]; omega
  rw [ht] at he hv
  exact ⟨he, hv.trans ha⟩

end Turing.MultiTapeATM.SourceWordInput
