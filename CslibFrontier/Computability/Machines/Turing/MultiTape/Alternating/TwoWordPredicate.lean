/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.AppendWord
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
import Mathlib.Tactic.FinCases

/-!
# Native predicates on two stored words

Two raw words on distinct work tapes are serialized once into the standard pair encoding.
The first word is framed, the second is appended without framing, and the destination is rewound
before the native predicate runs. The input-dependent predicate clock is retained: serialization
adds a linear term, rather than replacing the clock by a polynomial in the complete pair length.

## Main results

* `Turing.MultiTapeATM.TwoWordPredicate.exists_of_inO`: one finite alternating leaf evaluates a
  Boolean predicate from two stored words, charging both serialization and native execution.
* `Turing.MultiTapeATM.TwoWordPredicate.exists_of_host_inO`: the physical input tape supplies an
  additional encoded component at linear cost.
-/

public section

namespace Turing.MultiTapeATM.TwoWordPredicate

open MultiTapeTM

private def fields (x y : List Bool) : Fin 2 → List Bool := ![x, y]

private def prefixWord (x y : List Bool) : Fin 3 → List Bool :=
  ![[], frame x, frame x ++ y]

private def phaseTapes (i : Fin 2) : Fin 2 ↪ Fin 3 where
  toFun := ![i.castSucc, 2]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hi := i.isLt; have hv := congrArg Fin.val h; simp at hv; omega

@[simp] private theorem phaseTapes_source (i : Fin 2) : phaseTapes i 0 = i.castSucc := rfl

@[simp] private theorem phaseTapes_dest (i : Fin 2) : phaseTapes i 1 = Fin.last 2 := rfl

private noncomputable def phase (i : Fin 2) :=
  (AppendWord.machine (decide (i.val = 0))).extendTapes (phaseTapes i)

private def stage (input x y : List Bool) (n : Fin 3) : Cfg 3 Bool Unit input :=
  tapesCfg input (Fin.lastCases (prefixWord x y n) (fields x y)) 0
    (Fin.lastCases ((prefixWord x y n).length : ℤ)
      (fun i => if i.val < n.val then ((fields x y i).length : ℤ) else 0)) []

private theorem prefix_next (x y : List Bool) (i : Fin 2) :
    prefixWord x y i.succ = prefixWord x y i.castSucc ++
      AppendWord.fragment (decide (i.val = 0)) (fields x y i) := by
  fin_cases i <;> simp [prefixWord, fields, AppendWord.fragment]

private theorem runs_phase (input x y : List Bool) (i : Fin 2) :
    RunsBetween (phase i) (stage input x y i.castSucc) (stage input x y i.succ)
      (AppendWord.clock (decide (i.val = 0)) (fields x y i))
      (2 * (AppendWord.clock (decide (i.val = 0)) (fields x y i) + 1) + 1) := by
  have hv : viewCfg (phaseTapes i) (stage input x y i.castSucc) =
      AppendWord.config input (fields x y i) (prefixWord x y i.castSucc) 0 [] := by
    apply Cfg.ext <;> try rfl
    all_goals
      funext j
      fin_cases j <;>
        simp only [viewCfg, stage, tapesCfg, Nat.reduceAdd, Pi.zero_apply, sub_zero,
          Fin.val_castSucc, Fin.val_fin_lt, Fin.zero_eta, Fin.isValue, phaseTapes_source,
          Fin.lastCases_castSucc, AppendWord.config, CharP.cast_eq_zero, Matrix.cons_val_zero,
          Fin.mk_one, phaseTapes_dest, Fin.reduceLast, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, lt_self_iff_false, ↓reduceIte]
    all_goals rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
  have h := AppendWord.runsBetween (decide (i.val = 0)) input (fields x y i)
    (prefixWord x y i.castSucc) []
  rw [← hv] at h
  have he := h.extendTapes (phaseTapes i)
  have heq : embed (phaseTapes i)
      (AppendWord.config input (fields x y i)
        (prefixWord x y i.castSucc ++ AppendWord.fragment (decide (i.val = 0)) (fields x y i))
        (fields x y i).length [])
      (stage input x y i.castSucc).workTapes (stage input x y i.castSucc).workTapePos =
        stage input x y i.succ := by
    apply embed_tapesCfg
    · intro j
      fin_cases j <;>
        simp only [Nat.reduceAdd, prefix_next, Fin.val_eq_zero_iff, Fin.isValue, Fin.zero_eta,
          phaseTapes_source, Fin.lastCases_castSucc, Matrix.cons_val_zero, Pi.zero_apply,
          List.length_append, Nat.cast_add, Fin.val_succ, Order.lt_add_one_iff, Fin.val_fin_le,
          Std.le_refl, ↓reduceIte, and_self, Fin.mk_one, phaseTapes_dest, Fin.reduceLast,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, true_and]
      constructor <;> rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
    · intro j hj
      cases j using Fin.lastCases with
      | last => exact (hj ⟨1, rfl⟩).elim
      | cast j =>
        have hne : j ≠ i := by
          intro hji
          subst j
          exact hj ⟨0, rfl⟩
        have hv : j.val ≠ i.val := fun h => hne (Fin.ext h)
        simp only [Fin.lastCases_castSucc, Pi.zero_apply, Fin.val_castSucc,
          Fin.val_succ, true_and]
        split_ifs <;> (first | rfl | omega)
  rw [heq] at he
  exact he

private def finished (input x y : List Bool) : Cfg 3 Bool Unit input :=
  tapesCfg input (Fin.lastCases (frame x ++ y) (fields x y)) 0
    (Fin.lastCases 0 (fun i => ((fields x y i).length : ℤ))) []

private noncomputable def rewind :=
  (rewindWork Bool).extendTapes (tapeEmb (Fin.last 2))

private theorem runs_rewind (input x y : List Bool) :
    RunsBetween rewind (stage input x y 2) (finished input x y)
      ((frame x ++ y).length + 2) (3 * ((frame x ++ y).length + 3)) := by
  apply RunsBetween.of_runFrom
  simp only [rewind, runFrom_tapeEmb, oneTapeCfg, stage, tapesCfg, Cfg.withState,
    extendTapes_q₀, Pi.zero_apply, sub_zero, Fin.lastCases_last]
  rw [show prefixWord x y 2 = frame x ++ y from rfl,
    runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
  apply Cfg.ext <;> try rfl
  all_goals
    funext j
    cases j using Fin.lastCases with
    | last =>
      simp only [Nat.reduceAdd, Fin.reduceLast, Function.update_self, finished, tapesCfg,
        Pi.zero_apply, sub_zero, Fin.isValue, List.length_append, length_frame, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
        Order.lt_two_iff]
      rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
    | cast j =>
      have hn : j.castSucc ≠ (2 : Fin 3) := Fin.castSucc_ne_last j
      have hj : j.val ≤ 1 := by omega
      simp [finished, tapesCfg, hn, hj]

private noncomputable def serialize := ((phase 0).seq ((phase 1).seq rewind)).fromLeftBlank

private theorem runs_serialize (input x y : List Bool) :
    RunsBetween (input := input) serialize { stage input x y 0 with inputPos := 0 }
      { finished input x y with inputPos := 0 }
      (2 * (frame x ++ y).length + 5) (5 * (frame x ++ y).length + 29) := by
  have h := ((runs_phase input x y 0).seq
    ((runs_phase input x y 1).seq (runs_rewind input x y))).fromLeftBlank rfl rfl
  convert h using 1 <;> (first | rfl | (simp [AppendWord.clock, fields]; omega))

private def serializeTapes {k : ℕ} (dst : Fin k) : Fin 3 ↪ Fin (2 + k) where
  toFun := ![(0 : Fin 2).castAdd k, (1 : Fin 2).castAdd k, Fin.natAdd 2 dst]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hv := congrArg Fin.val h; dsimp at hv; omega

private def packed {k : ℕ} (dst : Fin k) (input word : List Bool) : Cfg k Bool Unit input :=
  { tapesCfg input (Function.update (fun _ => []) dst word) 0 0 [] with inputPos := 0 }

private noncomputable def packThen {k : ℕ} {S : Type} (dst : Fin k)
    (sub : MultiTapeATM k Bool S) :=
  prependTM (serialize.extendTapes (serializeTapes dst)) (sub.extendTapes (Fin.natAddEmb 2))

private theorem packThen_spec {k : ℕ} {S : Type} (dst : Fin k) (sub : MultiTapeATM k Bool S)
    (input x y : List Bool) (t : ℕ)
    (ht : sub.HaltsWithin t ((packed dst input (frame x ++ y)).withState
      (some sub.toPTM.initial))) :
    let atm := packThen dst sub
    let start := TwoWordInput.ready ((0 : Fin 2).castAdd k) ((1 : Fin 2).castAdd k) input x y
    let cfg := start.withState (some atm.toPTM.initial)
    let time := 2 * (frame x ++ y).length + 5 + t
    atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔
      sub.AcceptsWithin t ((packed dst input (frame x ++ y)).withState
        (some sub.toPTM.initial))) := by
  let i : Fin (2 + k) := (0 : Fin 2).castAdd k
  let j : Fin (2 + k) := (1 : Fin 2).castAdd k
  let E := serializeTapes dst
  let B : Fin k ↪ Fin (2 + k) := Fin.natAddEmb 2
  let start := TwoWordInput.ready i j input x y
  let finish : Cfg (2 + k) Bool Unit input :=
    embed E { finished input x y with inputPos := 0 }
    start.workTapes start.workTapePos
  have he (l : Fin 3) : E l = ![i, j, B dst] l := rfl
  have hv : viewCfg E start = { stage input x y 0 with inputPos := 0 } := by
    apply Cfg.ext <;> try rfl
    · funext l z
      simp only [viewCfg, start, TwoWordInput.ready, wordsCfg, stage, tapesCfg,
        Pi.zero_apply, sub_zero]
      cases l using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last]
        simp [TwoWordInput.words, he, B, i, j, prefixWord,
          (Fin.castAdd_ne_natAdd _ _).symm]
      | cast l =>
        rw [Fin.lastCases_castSucc]
        fin_cases l <;> simp [TwoWordInput.words, he, i, j, fields]
    · funext l
      simp only [viewCfg, start, TwoWordInput.ready, wordsCfg, stage, tapesCfg]
      cases l using Fin.lastCases with
      | last => rw [Fin.lastCases_last]; rfl
      | cast l =>
        rw [Fin.lastCases_castSucc]
        simp
  have hprep := runs_serialize input x y
  rw [← hv] at hprep
  have hprep' := hprep.extendTapes E
  have hnot (l : Fin k) (hl : l ≠ dst) : B l ∉ Set.range E := by
    rintro ⟨m, hm⟩
    fin_cases m
    · exact Fin.castAdd_ne_natAdd _ _ hm
    · exact Fin.castAdd_ne_natAdd _ _ hm
    · exact hl (B.injective hm).symm
  have hview : viewCfg B finish = packed dst input (frame x ++ y) := by
    apply Cfg.ext <;> try rfl
    · funext l
      by_cases hl : l = dst
      · subst l
        change finish.workTapes (E 2) = _
        dsimp only [finish]
        rw [embed_workTapes_embed]
        simp only [finished, tapesCfg, Nat.reduceAdd, Pi.zero_apply, sub_zero, Fin.isValue,
          packed, Function.update_self]
        rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
      · change finish.workTapes (B l) = _
        dsimp only [finish]
        rw [embed_workTapes_of_notMem_range _ _ _ _ (hnot l hl)]
        simp [start, TwoWordInput.ready, TwoWordInput.words, wordsCfg,
          packed, tapesCfg, B, i, j, hl,
          (Fin.castAdd_ne_natAdd _ _).symm]
    · funext l
      by_cases hl : l = dst
      · subst l
        change finish.workTapePos (E 2) = _
        dsimp only [finish]
        rw [embed_workTapePos_embed]
        simp only [finished, tapesCfg, Nat.reduceAdd, Pi.zero_apply, sub_zero, Fin.isValue,
          packed]
        rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
      · change finish.workTapePos (B l) = _
        dsimp only [finish]
        rw [embed_workTapePos_of_notMem_range _ _ _ _ (hnot l hl)]
        rfl
  have hv' : viewCfg B (finish.withState (some (sub.extendTapes B).toPTM.initial)) =
      (packed dst input (frame x ++ y)).withState (some sub.toPTM.initial) :=
    congrArg (fun d => d.withState (some sub.toPTM.initial)) hview
  have hh := (haltsWithin_extendTapes_iff sub B t _).mpr (hv' ▸ ht)
  obtain ⟨hh', ha⟩ := prependTM_spec _ (sub.extendTapes B) start finish _ t hprep'.1 hh
  exact ⟨hh', ha.trans ((acceptsWithin_extendTapes_iff sub B t _).trans
    (Iff.of_eq (congrArg (sub.AcceptsWithin t) hv')))⟩

/-- A native predicate on a pair can start with its two components on separate work tapes.
The same finite alternating machine works for every pair and every host input. Framing, copying,
rewinding and the normalized predicate computation all appear in the common linear-plus-`T`
clock; the separate space certificate is used only by the native predicate normalization. -/
theorem exists_of_inO {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α × β → Bool} {T W : α × β → ℕ}
    (hf : ComputableInO f (encPair encA encB) encBool T W) :
    ∃ (K : ℕ) (i j : Fin K) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM K Bool Q) (c : ℕ),
      i ≠ j ∧ ∀ (input : List Bool) (a : α) (b : β),
        let cfg := (TwoWordInput.ready i j input (encA a) (encB b)).withState
          (some atm.toPTM.initial)
        let time := c * ((encPair encA encB (a, b)).length + T (a, b) + 1)
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔ f (a, b) = true) := by
  obtain ⟨k, S, hS, tm, c, hr⟩ := WorkTapePredicate.exists_of_inO hf
  let sub := MultiTapeATM.ofTMs (fun _ => tm) (fun _ => false)
  let dst : Fin (k + 2) := Fin.natAdd k 0
  refine ⟨_, (0 : Fin 2).castAdd (k + 2), (1 : Fin 2).castAdd (k + 2), _, inferInstance,
    packThen dst sub, c + 5, ?_, ?_⟩
  · exact fun h => absurd (congrArg Fin.val h) (by decide : (0 : ℕ) ≠ 1)
  intro input a b
  dsimp only
  let pair := encPair encA encB (a, b)
  let cfg := (packed dst input pair).withState (some sub.toPTM.initial)
  have hh : sub.HaltsWithin (c * (T (a, b) + 1)) cfg := by
    rw [haltsWithin_ofTMs_const_iff]
    change (tm.runFrom ((WorkTapePredicate.config input pair).withState (some tm.q₀)) _).state =
      none
    rw [hr]
    rfl
  have ha : sub.AcceptsWithin (c * (T (a, b) + 1)) cfg ↔ f (a, b) = true := by
    rw [acceptsWithin_ofTMs_const_iff]
    change ((tm.runFrom ((WorkTapePredicate.config input pair).withState (some tm.q₀)) _).state =
      none ∧ _) ↔ _
    change _ ∧
      (tm.runFrom ((WorkTapePredicate.config input pair).withState (some tm.q₀)) _).output =
        [true] ↔ _
    rw [hr]
    simp [WorkTapePredicate.config, Cfg.withState, tapesCfg]
  obtain ⟨hp, he⟩ := packThen_spec dst sub input (encA a) (encB b) _ hh
  have hb : 2 * pair.length + 5 + c * (T (a, b) + 1) ≤
      (c + 5) * (pair.length + T (a, b) + 1) := by nlinarith
  exact ⟨hp.mono hb, ⟨fun h => ha.mp (he.mp (h.of_halted_stepCoins hp)),
    fun h => (he.mpr (ha.mpr h)).mono hb⟩⟩

/-- Evaluate a certified predicate on the encoded host input and two stored words. First
serialize the stored pair, then copy the physical input onto the other predicate tape. Each
physical field contributes linearly to preparation, in addition to the claimed predicate time. -/
theorem exists_of_host_inO {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α × β × γ → Bool} {T W : α × β × γ → ℕ}
    (hf : ComputableInO f (encPair encA (encPair encB encC)) encBool T W) :
    ∃ (U : ℕ) (src query : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C : ℕ),
      src ≠ query ∧ ∀ (a : α) (b : β) (q : γ),
        let cfg := (TwoWordInput.ready src query (encA a) (encB b) (encC q)).withState
          (some atm.toPTM.initial)
        let time := C * ((encA a).length + (encB b).length + (encC q).length + T (a, b, q) + 1)
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔ f (a, b, q) = true) := by
  obtain ⟨k, i, j, S, hS, sub, c, hij, hsub⟩ := exists_of_inO hf
  let loader := (loadWord Bool i).fromLeftBlank
  let run := prependTM loader sub
  refine ⟨_, (0 : Fin 2).castAdd k, (1 : Fin 2).castAdd k, _, inferInstance,
    packThen j run, 4 * c + 16, ?_, ?_⟩
  · exact fun h => absurd (congrArg Fin.val h) (by decide : (0 : ℕ) ≠ 1)
  intro a b q
  dsimp only
  let host := encA a
  let pair := encPair encB encC (b, q)
  let ws := Function.update (fun _ : Fin k => ([] : List Bool)) j pair
  obtain ⟨_, _, ⟨rfl, rfl⟩, hload⟩ := RunsBetween.of_transformsTapes
    (input := host) (transformsTapes_loadWord i host) (ws := ws)
    ⟨rfl, Function.update_of_ne hij _ _⟩ 0 []
  have hw : Function.update ws i host = TwoWordInput.words i j host pair := by
    funext l
    simp only [ws, Function.update_apply, TwoWordInput.words]
  rw [hw] at hload
  have hfinish : { tapesCfg host (TwoWordInput.words i j host pair) 0 0 [] with inputPos := 0 } =
      TwoWordInput.ready i j host host pair := by
    apply Cfg.ext <;> try rfl
    funext l z
    simp [TwoWordInput.ready, wordsCfg, tapesCfg]
  have hr : loader.runFrom ((packed j host pair).withState (some loader.q₀))
      (3 * host.length + 6 + 2) = (TwoWordInput.ready i j host host pair).withState none := by
    rw [← hfinish]
    exact (hload.fromLeftBlank rfl rfl).1
  have hs := hsub host a (b, q)
  obtain ⟨hh, ha⟩ := prependTM_spec loader sub (packed j host pair)
    (TwoWordInput.ready i j host host pair) _ _ hr hs.1
  obtain ⟨hp, he⟩ := packThen_spec j run host (encB b) (encC q) _ hh
  have hb : 2 * pair.length + 5 + (3 * host.length + 6 + 2 + c *
      ((encPair encA (encPair encB encC) (a, b, q)).length + T (a, b, q) + 1)) ≤
      (4 * c + 16) * (host.length + (encB b).length + (encC q).length + T (a, b, q) + 1) := by
    simp only [pair, host, length_encPair]
    nlinarith
  exact ⟨hp.mono hb, ⟨fun h => hs.2.mp (ha.mp (he.mp (h.of_halted_stepCoins hp))),
    fun h => (he.mpr (ha.mpr (hs.2.mpr h))).mono hb⟩⟩

end Turing.MultiTapeATM.TwoWordPredicate
