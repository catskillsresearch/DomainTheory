/-ai
Every unary primitive-recursive function p has a combinatory element that realizes it.

Proceed by induction on the primitive-recursive derivation. The zero function is realized by the constant combinator constComb 0. Successor is realized by sucC, using sucC_app and succSet_ofNat. The left and right unpairing projections are realized by unpairFstC and unpairSndC. A pairing of two realized functions is realized by pairRealizer, a composition by composeC, and a primitive recursion by precC, using the corresponding combinatory and realization lemmas.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.composeC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.composeC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.constComb_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.constComb_realizes
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.pairRealizer_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.pairRealizer_realizes
public import DomainTheory.DataTypesAsLattices.Computability.precC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.precC_realizes

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


/-- Every unary primitive-recursive function has a combinatory realizer. -/
theorem primrec_realized {p : ℕ → ℕ} (hp : Nat.Primrec p) :
    ∃ u, IsCombinatory u ∧ Realizes u p := by
  induction hp with
  | zero =>
      exact ⟨constComb 0, constComb_combinatory 0, constComb_realizes 0⟩
  | succ =>
      exact ⟨sucC, .suc, fun n => by rw [sucC_app, succSet_ofNat]⟩
  | left =>
      exact ⟨unpairFstC, unpairFstC_combinatory, unpairFstC_realizes⟩
  | right =>
      exact ⟨unpairSndC, unpairSndC_combinatory, unpairSndC_realizes⟩
  | pair _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨pairRealizer u v, pairRealizer_combinatory hu hv,
        pairRealizer_realizes hru hrv⟩
  | comp _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨composeC u v, composeC_combinatory hu hv, composeC_realizes hru hrv⟩
  | prec _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨precC u v, precC_combinatory hu hv, precC_realizes hru hrv⟩

end DomainTheory.DataTypesAsLattices
