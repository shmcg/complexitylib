import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SourceWordInput

open Turing Turing.MultiTapeTM Turing.MultiTapeATM

private def readFirst : MultiTapeTM 1 Bool Bool :=
  ofTr false fun phase symbol _ => if phase then
    ⟨0, fun _ => (none, 0), some (symbol.getD false), none⟩
    else ⟨1, fun _ => (none, 0), none, some true⟩

private noncomputable def child : MultiTapeATM 1 Bool Bool :=
  ofTMs (fun _ => readFirst) (fun _ => false)

private theorem read_first (x ch : List Bool) :
    let start := SharedWordFork.start 0 child x ch 0
    child.HaltsWithin 2 start ∧ (child.AcceptsWithin 2 start ↔ x.head? = some true) := by
  intro start
  have h (b : Bool) (c : Cfg 1 Bool Bool x) : child.next b c = readFirst.step c :=
    next_ofTMs _ _ b c
  have hs : start.state = some false := by simp [start, child, SharedWordFork.start,
    WordGameLeaf.config, ofTMs, readFirst]
  have h₁ : (readFirst.step start).state = some true := by
    simp [step_of_state hs, readFirst, Action.apply]
  have h₂ : (readFirst.step (readFirst.step start)).state = none := by
    rw [step_of_state h₁]
    simp [readFirst, Action.apply]
  refine ⟨by simp [haltsWithin_succ, h, haltsWithin_zero, h₂], ?_⟩
  simp only [AcceptsWithin, hs, h₁, h₂, h, true_and]
  change (if false then _ else _) ↔ _
  simp only [Bool.false_eq_true, ↓reduceIte, exists_const]
  rw [step_of_state h₁, step_of_state hs]
  cases x with
  | nil => simp [readFirst, start, Cfg.inputSymbol, Action.apply, moveInputPos,
      SharedWordFork.start, WordGameLeaf.config, TwoWordLoad.blank, tapesCfg]
  | cons a as =>
    cases a <;> simp [readFirst, start, Cfg.inputSymbol, Action.apply, moveInputPos,
      SharedWordFork.start, WordGameLeaf.config, TwoWordLoad.blank, tapesCfg]

-- The two possible first source symbols and the empty source are all covered by one external ATM.
example : ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C : ℕ),
    ∀ (ch x : List Bool),
      let input := encPair encBits encBits (ch, x)
      let time := C * (x.length + ch.length + 1) + 2
      atm.HaltsWithin time (atm.toPTM.toNTM.initCfg input) ∧
        (atm.AcceptsWithin time (atm.toPTM.toNTM.initCfg input) ↔ x.head? = some true) := by
  obtain ⟨u, Q, hQ, atm, C, h⟩ := SourceWordInput.exists_prepend encBits 0 child
  refine ⟨u, Q, hQ, atm, C, fun ch x => ?_⟩
  obtain ⟨ht, ha⟩ := h ch x 2 (read_first x ch).1
  exact ⟨ht, ha.trans (read_first x ch).2⟩

-- A stored pair supplies the source seen by the child, for every outer host and head position.
-- Empty and rejecting payloads are included even when the host begins with true.
example : ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM U Bool Q) (C : ℕ), ∀ (host ch x : List Bool) (pos : ℕ),
      let word := encPair encBits encBits (ch, x)
      let time := pos + C * (word.length + 1) + 12
      let start := SharedWordFork.start src atm host word pos
      pos ≤ word.length → atm.HaltsWithin time start ∧
        (atm.AcceptsWithin time start ↔ x.head? = some true) := by
  have hf : ComputableInO (Prod.fst : List Bool × List Bool → List Bool)
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length) (fun p => (encPair encBits encBits p).length) :=
    .of_linear (PairEncoding.fst (enc₁ := encBits) (enc₂ := encBits))
  have hs : ComputableInO (Prod.snd : List Bool × List Bool → List Bool)
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length) (fun p => (encPair encBits encBits p).length) :=
    .of_linear (PairEncoding.snd (enc₁ := encBits) (enc₂ := encBits))
  obtain ⟨U, src, Q, hQ, atm, C, h⟩ := SourceWordInput.exists_prepend_work hf hs 0 child
  refine ⟨U, src, Q, hQ, atm, C, ?_⟩
  intro host ch x pos word time start hpos
  obtain ⟨hh, ha⟩ := h host (ch, x) pos hpos 2 (read_first x ch).1
  exact ⟨hh, ha.trans (read_first x ch).2⟩
