/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qDen_pos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qDen_ratMidCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

























/-- **Correctness of `ratMidCode`**: it decodes to the arithmetic mean of the two decoded
rationals. -/
theorem decodeRat_ratMidCode (c1 c2 : ℕ) :
    decodeRat (ratMidCode (Nat.pair c1 c2)) = (decodeRat c1 + decodeRat c2) / 2 := by
  have hqnp : qNumP (ratMidCode (Nat.pair c1 c2)) =
      qNumP c1 * qDen c2 + qNumP c2 * qDen c1 := by
    show (ratMidCode (Nat.pair c1 c2)).unpair.1.unpair.1 = _
    simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  have hqnn : qNumN (ratMidCode (Nat.pair c1 c2)) =
      qNumN c1 * qDen c2 + qNumN c2 * qDen c1 := by
    show (ratMidCode (Nat.pair c1 c2)).unpair.1.unpair.2 = _
    simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_eq, hqnp, hqnn, qDen_ratMidCode, Rat.mkRat_eq_div,
    decodeRat_eq c1, decodeRat_eq c2, Rat.mkRat_eq_div, Rat.mkRat_eq_div]
  have hd1 : (qDen c1 : ℚ) ≠ 0 := by exact_mod_cast (qDen_pos c1).ne'
  have hd2 : (qDen c2 : ℚ) ≠ 0 := by exact_mod_cast (qDen_pos c2).ne'
  push_cast
  field_simp
  ring

end DomainTheory.NeighbourhoodSystems
