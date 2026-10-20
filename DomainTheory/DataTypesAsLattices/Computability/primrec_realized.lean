/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.composeC_combinatory
import DomainTheory.DataTypesAsLattices.Computability.composeC_realizes
import DomainTheory.DataTypesAsLattices.Computability.constComb_combinatory
import DomainTheory.DataTypesAsLattices.Computability.constComb_realizes
import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_combinatory
import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_combinatory
import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_realizes
import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_realizes
import DomainTheory.DataTypesAsLattices.Computability.pairRealizer_combinatory
import DomainTheory.DataTypesAsLattices.Computability.pairRealizer_realizes
import DomainTheory.DataTypesAsLattices.Computability.precC_combinatory
import DomainTheory.DataTypesAsLattices.Computability.precC_realizes


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
