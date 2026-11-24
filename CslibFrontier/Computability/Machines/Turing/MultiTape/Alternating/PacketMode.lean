/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.PacketModeInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StoppingSum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SourceWordInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordPredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.BinarySlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size

/-!
# Native bit queries for the sum defining a packet mode

One stored word supplies the stopping request, the packet's ordered port tags and its bits.
The assignment path selects one original port. Two binary lookups retrieve that tag and bit
before the scalar computation begins. Only the selected slot, short mode and circuit metadata,
and binary lengths of the two long words enter the polynomial part of the clock.
-/

public section

namespace Turing.MultiTapeATM.PacketMode

open MultiTapeTM Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Frontier
open FastContraction StoppingQuery.ProductRouting PacketModeInput

/-- Original port tags with their local assignment and the requested packet mode. -/
structure Payload where
  /-- Short mode metadata. -/
  context : PacketModeInput.Context
  /-- Ordered pairs of the row flag and the binary slot index. -/
  tags : List (Bool × ℕ)
  /-- One local bit per port, defaulting to false on truncated data. -/
  bits : List Bool

/-- A framed row flag followed by the binary slot. -/
abbrev encTag := encPair encBool encNat

/-- The mode header and ordered tag list are framed. The local assignment is a raw suffix. -/
enc_structure encPayload : Payload where
  context : PacketModeInput.encContext, tags : (encList encTag), bits : encBits

private noncomputable abbrev encPathPos := encPair encBits encPosition
private noncomputable abbrev encLeaf := encPair encPayload encPathPos
private abbrev Leaf := Payload × (List Bool × Position)

private def atPort (a : Payload) (j : ℕ) := a.tags.getD j (true, 0)

private noncomputable def answer : Leaf → Bool := fun (a, path, p) =>
  check a.context (atPort a (binaryValue path)) (a.bits.getD (binaryValue path) false) p

/-- Size used by the terminal polynomial. The two complete port words contribute only their
binary lengths, and `slotWidth` bounds the binary size of a selected slot. -/
@[expose] def shortSize (a : Payload) (pathLength positionLength slotWidth : ℕ) : ℕ :=
  8 * ((PacketModeInput.encContext a.context).length + (encList encTag a.tags).length.size +
    a.bits.length.size + pathLength + positionLength + slotWidth + 1) + 16

private noncomputable def short (x : Leaf) : ℕ :=
  let (a, path, p) := x
  shortSize a path.length (encPosition p).length (atPort a (binaryValue path)).2.size

private theorem exists_answer_inO : ∃ D, ComputableInO answer encLeaf encBool
    (fun x => (encPayload x.1).length + short x ^ D)
    (fun x => (encPayload x.1).length + short x ^ D) := by
  let host := ComputableInDegree.fst encPayload encPathPos
  let arg := ComputableInDegree.snd encPayload encPathPos
  have hc := (encPayload_context_deg.comp host).mono (d' := 1) (e' := 1)
  have ht := (encPayload_tags_deg.comp host).mono (d' := 1) (e' := 1)
  have hb := (encPayload_bits_deg.comp host).mono (d' := 1) (e' := 1)
  have hw := ((ComputableInDegree.fst encBits encPosition).comp arg).mono (d' := 1) (e' := 1)
  have hp := ((ComputableInDegree.snd encBits encPosition).comp arg).mono (d' := 1) (e' := 1)
  obtain ⟨di, _, hindex⟩ := ComputableInPolyTime.bitsBinaryValue.exists_degree
  have hi := hindex.inO.comp hw.inO_one
  obtain ⟨dt, htag⟩ := ComputableInO.exists_listGetElem?_binary encTag
  obtain ⟨db, hbit⟩ := ComputableInO.exists_bitsGetD_binary
  have hport := (htag.comp (ht.inO_one.prod hi)).optionGetD (true, 0)
  have hlocal := hbit.comp (hb.inO_one.prod hi)
  let encSelected :=
    encPair (encPair PacketModeInput.encContext encTag) (encPair encBool encPosition)
  have hfinish : ComputableInPolyTime
      (fun x : (PacketModeInput.Context × (Bool × ℕ)) × (Bool × Position) =>
        check x.1.1 x.1.2 x.2.1 x.2.2) encSelected encBool := by
    apply check_polyTime <;> dsimp only [encSelected] <;> fun_prop
  obtain ⟨df, _, hf⟩ := hfinish.exists_degree
  have h := hf.inO.comp ((hc.inO_one.prod hport).prod (hlocal.prod hp.inO_one))
  let D := max 1 (max di (max dt (max db df)))
  refine ⟨D, (h.of_enc_eq (g := answer) ?_).mono 40 ?_ ?_⟩
  · rintro ⟨a, path, p⟩
    simp [answer, atPort, List.getD_eq_getElem?_getD]
  all_goals
    rintro ⟨a, path, p⟩
    let s := short (a, path, p)
    have hs : 0 < s := by simp [s, short, shortSize]
    have hj := Nat.size_le.mpr (binaryValue_lt_two_pow path)
    have hupper (v e : ℕ) (hv : v ≤ s) (he : e ≤ D) : v ^ e ≤ s ^ D :=
      (Nat.pow_le_pow_left hv e).trans (Nat.pow_le_pow_right hs he)
    have hsD : s ≤ s ^ D := by
      simpa only [pow_one] using hupper s 1 le_rfl (Nat.le_max_left ..)
    have hi' := hupper (path.length + 1) di (by dsimp only [s, short, shortSize]; omega)
      (by dsimp [D]; omega)
    have ht' := hupper ((encList encTag a.tags).length.size + (binaryValue path).size + 1) dt
      (by dsimp [s, short, shortSize]; omega) (by dsimp [D]; omega)
    have hb' := hupper (a.bits.length.size + (binaryValue path).size + 1) db
      (by dsimp [s, short, shortSize]; omega) (by dsimp [D]; omega)
    have hf' := hupper ((encSelected ((a.context, atPort a (binaryValue path)),
      (a.bits.getD (binaryValue path) false, p))).length + 1) df (by
        simp only [encSelected, encTag, length_encPair, encNat_apply, ← Nat.size_eq_bits_len,
          encBool_apply, List.length_singleton, s, short, shortSize]; omega) (by dsimp [D]; omega)
    have hin : (encLeaf (a, path, p)).length ≤ 2 * (encPayload a).length + s := by
      simp only [encLeaf, encPathPos, length_encPair, encBits_apply, s, short, shortSize]; omega
    have htlen : (encList encTag a.tags).length + a.bits.length ≤ (encPayload a).length := by
      simp only [encPayload_apply, encPayloadFields, length_encPair, encBits_apply]; omega
    simp only [Function.comp_apply, encBits_apply, ← List.getD_eq_getElem?_getD] at *
    change _ ≤ 40 * ((encPayload a).length + s ^ D + 1)
    dsimp only [encLeaf] at hin
    dsimp only [atPort] at hf'
    omega

private theorem atPort_size_le (a : Payload) (width j : ℕ)
    (h : ∀ tag ∈ a.tags, tag.2 < 2 ^ width) : (atPort a j).2.size ≤ width := by
  by_cases hj : j < a.tags.length
  · rw [atPort, List.getD_eq_getElem _ _ hj]
    exact Nat.size_le.mpr (h _ (List.getElem_mem _))
  · rw [atPort, List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    exact Nat.zero_le _

/-- The terminal's uniform clock on a valid product path. The selected slot width is a bound
on the actual packet data. The exponent controls only the number of product vertices. -/
@[expose] noncomputable def terminalTime (c d : ℕ) (a : Payload) (width L : ℕ)
    (params : StoppingQuery.Product.Parameters) : ℕ :=
  let H := CarrySaveCountingRoot.sizeBudget (2 ^ L) params.precision
  let levels := Nat.clog 2 params.vertices
  let M := metadataBound params (2 ^ levels) levels
  let s := shortSize a H M width
  c * (4 * (encPayload a).length + 4 * s + s ^ d + 4)

/-- One fixed finite machine checks a representative bit of the actual packet mode sum.
It reads the stopping request and the original port data from one work tape at any valid
cursor, with an arbitrary outer input. The loader and terminal charge the port data linearly.
The height is the bit length of the encoded tag-list length. -/
theorem exists_evaluator :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q)
      (J C D P E A F : ℕ), ∀ (host : List Bool) (a : Payload) (m w width : ℕ),
      (∀ tag ∈ a.tags, tag.2 < 2 ^ width) →
      ∀ (k : Fin (modulus m).length) (b : Fin w) (claim : Bool),
        let params : StoppingQuery.Product.Parameters := ⟨m, w, a.context.exponent + 1⟩
        let ctx : StoppingLeafRequest.Context := ⟨params, k.val⟩
        let L := (encList encTag a.tags).length.size
        let req : CarrySaveWordSum.Request := ⟨StoppingLeafRequest.encContext ctx, L, ⟨w, b, claim⟩⟩
        let word := encPair CarrySaveWordSum.encRequest encPayload (req, a)
        ∀ pos, pos ≤ word.length →
        let start := SharedWordFork.start src atm host word pos
        let time := pos + J * (word.length + 1) + 10 + (C * (L +
          ((StoppingLeafRequest.encContext ctx).length + L.size + w.size + 1) ^ D + 1) +
          StoppingProduct.clock P E params (terminalTime A F a width L params))
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          ((representative m w (GaloisRingArith.val w (modulus m)
            (NativePacket.modeValueList w (modulus m) a.context.coordinate a.context.differ
              (NativePacket.sidePorts a.tags a.bits false) a.context.tile
              a.context.exponent))).coeff k.val).val.testBit b.val = claim) := by
  obtain ⟨F, hf⟩ := exists_answer_inO
  obtain ⟨N, ass, query, S, hS, leaf, A, hne, ht⟩ :=
    TwoWordPredicate.exists_of_host_inO hf
  let := hS
  obtain ⟨K, i, S', hS', child, C, D, P, E, hs⟩ :=
    StoppingSum.exists_evaluator ass query hne leaf
  let := hS'
  let enc := encPair CarrySaveWordSum.encRequest encPayload
  have hr := (ComputableInDegree.fst CarrySaveWordSum.encRequest encPayload).inO_one
  have hp := (ComputableInDegree.snd CarrySaveWordSum.encRequest encPayload).inO_one
  have hv : ComputableInO (fun x : CarrySaveWordSum.Request × Payload => encPayload x.2)
      enc encBits (fun x => (enc x).length) (fun x => (enc x).length) :=
    hp.of_enc_eq fun _ => rfl
  obtain ⟨U, src, Q, hQ, atm, J, hload⟩ := SourceWordInput.exists_prepend_work hr hv i child
  refine ⟨U, src, Q, hQ, atm, J, C, D, P, E, A, F, ?_⟩
  intro host a m w width hwidth k b claim params ctx L req word pos hpos start time
  let entry (j v : ℕ) : GaloisRingArith.Ring w (modulus m) :=
    NativePacket.PacketWordSum.modeScalarFactor a.context.coordinate a.context.tile
      a.context.exponent a.context.differ (atPort a j) (a.bits.getD j false) v
  have h := hs (encPayload a) L params entry (terminalTime A F a width L params) (by
    intro path hpath p hp hterminal
    obtain ⟨hh, ha⟩ := ht a path p
    let M := metadataBound params (2 ^ Nat.clog 2 params.vertices) (Nat.clog 2 params.vertices)
    let H := CarrySaveCountingRoot.sizeBudget (2 ^ L) params.precision
    have hpos : (encPosition p).length ≤ M := hp.length_encPosition_le
    have hslot := atPort_size_le a width (binaryValue path) hwidth
    have hshort : short (a, path, p) ≤ shortSize a H M width := by
      change path.length ≤ H at hpath
      dsimp only [short, shortSize]; omega
    have hpow := Nat.pow_le_pow_left hshort F
    have htime : A * ((encPayload a).length + path.length + (encPosition p).length +
        ((encPayload a).length + short (a, path, p) ^ F) + 1) ≤
        terminalTime A F a width L params := by
      apply Nat.mul_le_mul_left
      change _ ≤ 4 * (encPayload a).length + 4 * shortSize a H M width +
        shortSize a H M width ^ F + 4
      change path.length ≤ H at hpath
      dsimp only [shortSize] at *; omega
    have hv := check_iff_value a.context (atPort a (binaryValue path))
      (a.bits.getD (binaryValue path) false) p hterminal
    rw [hp.parameters] at hv
    have hterminalValue := ha.trans hv
    exact ⟨hh.mono htime, ⟨fun hacc => hterminalValue.mp (hacc.of_halted_stepCoins hh),
      fun hacc => (hterminalValue.mpr hacc).mono htime⟩⟩) k b claim
  have hlen := SizedListEncoding.length_le (encA := encTag)
    (encL := encList encTag) a.tags
  have heq := NativePacket.PacketWordSum.sum_modeScalarFactor w (modulus m)
    a.context.coordinate a.context.tile a.context.exponent a.context.differ a.tags a.bits
    (2 ^ L) (hlen.trans (Nat.lt_size_self _).le)
  change (∑ j ∈ Finset.range (2 ^ L), ∏ v ∈ Finset.range params.vertices, entry j v) = _ at heq
  obtain ⟨halted, accepted⟩ := hload host (req, a) pos hpos _ h.1
  exact ⟨halted, accepted.trans (h.2.trans (by rw [heq]))⟩

end Turing.MultiTapeATM.PacketMode
