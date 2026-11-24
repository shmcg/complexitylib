/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.PacketMode

/-! # An actual stored packet whose mode bit changes with its local assignment -/

public section

namespace Turing.MultiTapeATM.PacketMode.Tests

open MultiTapeTM
open Cslib Cslib.Circuits.Frontier FastContraction NativePacket

/-- A single eligible column whose mode value is its local assignment bit. -/
@[expose] def oneColumn (localBit : Bool) : Payload :=
  ⟨⟨0, 0, 0, true⟩, [(false, 0)], [localBit]⟩

private def request (claim : Bool) : CarrySaveWordSum.Request :=
  ⟨StoppingLeafRequest.encContext ⟨⟨0, 1, 1⟩, 0⟩,
    (encList encTag (oneColumn true).tags).length.size, ⟨1, 0, claim⟩⟩

private theorem mode_bit (localBit : Bool) :
    ((representative 0 1 (GaloisRingArith.val 1 (modulus 0)
      (modeValueList 1 (modulus 0) 0 true
        (sidePorts (oneColumn localBit).tags (oneColumn localBit).bits false) 0 0))).coeff
          0).val.testBit 0 =
        localBit := by
  have h := PacketWordSum.sum_modeScalarFactor 1 (modulus 0) 0 0 0 true
    (oneColumn localBit).tags (oneColumn localBit).bits 1 (by simp [oneColumn])
  rw [← h, Finset.sum_range_one, Finset.prod_range_one]
  have hb (n : ℤ) := ScalarInput.representative_shiftedInt_bit 0 1 0 0 0 n
  cases localBit
  · simpa [PacketWordSum.modeScalarFactor, oneColumn, Int.testBit] using hb 0
  · simpa [PacketWordSum.modeScalarFactor, oneColumn, Int.testBit] using hb 1

-- The packet and control request begin together on one work tape. The same machine handles
-- both port bits and both claims at any initial cursor, independently of the outer host.
example : ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q),
    ∀ (host : List Bool) (localBit claim : Bool) (pos : ℕ),
      let word := encPair CarrySaveWordSum.encRequest encPayload (request claim, oneColumn localBit)
      pos ≤ word.length → ∃ t, let start := SharedWordFork.start src atm host word pos
        atm.HaltsWithin t start ∧ (atm.AcceptsWithin t start ↔ localBit = claim) := by
  obtain ⟨U, src, Q, hQ, atm, J, C, D, P, E, A, F, h⟩ := PacketMode.exists_evaluator
  refine ⟨U, src, Q, hQ, atm, ?_⟩
  intro host localBit claim pos word hpos
  have hslots : ∀ tag ∈ (oneColumn localBit).tags, tag.2 < 2 ^ 0 := by simp [oneColumn]
  obtain ⟨halted, correct⟩ := h host (oneColumn localBit) 0 1 0 hslots ⟨0, by decide⟩
    ⟨0, by decide⟩ claim pos hpos
  refine ⟨_, halted, correct.trans ?_⟩
  exact iff_of_eq (congrArg (fun bit => bit = claim) (mode_bit localBit))

end Turing.MultiTapeATM.PacketMode.Tests
