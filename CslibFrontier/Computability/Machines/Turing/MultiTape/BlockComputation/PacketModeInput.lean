/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.PacketWordSum
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ScalarInput
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.Routing
import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RouteTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Reading one scalar input of a packet mode

After selecting an ordered port tag and its local bit, `check` answers a stopping-product
terminal position. It handles Boolean constants and reads a scalar bit from the port's slot
quotient or eligibility indicator. The precision, exponent and requested bit are binary.
`check_iff_value` identifies the result with the circuit at every terminal position, and
`check_polyTime` implements it on the selected fields.
-/

public section

namespace Turing.MultiTapeTM.PacketModeInput

open Cslib Cslib.Circuits Cslib.Circuits.Frontier NativePacket.PacketWordSum FastContraction
open StoppingQuery StoppingQuery.Product StoppingQuery.ProductRouting ComputableInPolyTime

/-- Metadata shared by the port summands of one packet mode. -/
structure Context where
  /-- Number of low slot bits in addition to the lowest one. -/
  coordinate : ℕ
  /-- Required low-bit residue of the slot. -/
  tile : ℕ
  /-- Number of copies of the slot quotient in each product. -/
  exponent : ℕ
  /-- Whether the packet symbols differ. -/
  differ : Bool

/-- Framed unary coordinate, binary tile and binary exponent, followed by the symbol bit. -/
enc_structure encContext : Context where
  coordinate : encUnary, tile : encNat, exponent : encNat, differ : encBool

private def query (c : Context) (tag : Bool × ℕ) (localBit : Bool) (p : Position) :
    ScalarInput.Input :=
  ⟨modeScalarFactor c.coordinate c.tile c.exponent c.differ tag localBit p.data.base,
    0, p.parameters.precision, p.data.coefficient, p.data.bit, p.claim⟩

/-- Answer the claimed bit at a mode terminal using the selected port and the existing
signed scalar checker. The query shift is zero. -/
noncomputable def check (c : Context) (tag : Bool × ℕ) (localBit : Bool) (p : Position) : Bool :=
  decide (terminalValue (fun _ => ScalarInput.run (query c tag localBit p)) p = p.claim)

/-- The selected-port checker agrees with the value of every terminal, including constants. -/
theorem check_iff_value (c : Context) (tag : Bool × ℕ) (localBit : Bool) (p : Position)
    (hp : player p = none) :
    check c tag localBit p = true ↔
      StoppingQuery.value p.parameters.scale p.parameters.precision 0 p.parameters.vertices
        (fun _ v => (modeScalarFactor c.coordinate c.tile c.exponent c.differ tag localBit v :
          GaloisRingArith.Ring p.parameters.precision (modulus p.parameters.scale)))
        (address p) = p.claim := by
  rw [terminal_value _ _ hp]
  simp only [check, decide_eq_true_eq, terminalValue]
  by_cases he : p.data.kind = 4
  · simp only [he, ↓reduceIte, ScalarInput.run_eq_representative_bit p.parameters.scale, query,
      pow_zero, mul_one, Int.cast_natCast, entryBit]
  · simp only [he, ↓reduceIte]

/-- Polynomial-time evaluation after the caller has selected one tag and bit. Only the
coordinate is unary. The bound on a selected slot in an actual packet is supplied by its
descriptor when this certificate is placed inside a long-input clock. -/
theorem check_polyTime {α : Type} {enc : α ↪ List Bool} {c : α → Context}
    {tag : α → Bool × ℕ} {localBit : α → Bool} {pos : α → Position}
    (hc : ComputableInPolyTime c enc encContext)
    (htag : ComputableInPolyTime tag enc (encPair encBool encNat))
    (hbit : ComputableInPolyTime localBit enc encBool)
    (hp : ComputableInPolyTime pos enc encPosition) :
    ComputableInPolyTime (fun x => check (c x) (tag x) (localBit x) (pos x)) enc encBool := by
  have hd := encPosition_data_polyTime hp
  have hclaim := encPosition_claim_polyTime hp
  have hslot := (snd encBool encNat).comp htag
  have hstride := binary_two_pow.comp (unary_succ.comp (encContext_coordinate_polyTime hc))
  have heligible := decide_and (decide_eq' ((fst encBool encNat).comp htag) (const false))
    (decide_and (decide_eq' hbit (const true)) (decide_and
      (decide_eq' (encContext_differ_polyTime hc) (const true))
      (decide_eq' (binary_mod' hslot hstride) (encContext_tile_polyTime hc))))
  have hscalar := ite_decide
    (binary_lt' (encNodeData_base_polyTime hd) (encContext_exponent_polyTime hc))
    (binary_div' hslot hstride) (ite_decide heligible (const 1) (const 0))
  have hq : ComputableInPolyTime (fun x => query (c x) (tag x) (localBit x) (pos x))
      enc ScalarInput.encInput :=
    ScalarInput.encInput_mk_polyTime (intBin_natCast.comp hscalar) (const 0)
      (encParameters_precision_polyTime (encPosition_parameters_polyTime hp))
      (encNodeData_coefficient_polyTime hd) (encNodeData_bit_polyTime hd) hclaim
  have hop := of_finite (encIn := Boolean.encOp) (encOut := encBool)
    (fun op : Boolean.Op => match op with | .const b => b | _ => false)
  exact decide_eq' (ite_decide (decide_eq' (encNodeData_kind_polyTime hd) (const 4))
    (ScalarInput.computableInPolyTime_run.comp hq) (hop.comp (operation_polyTime.comp hp))) hclaim

end Turing.MultiTapeTM.PacketModeInput
