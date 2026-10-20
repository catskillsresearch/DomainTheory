/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qNumP
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qNumN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qDen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The `{0,1}`-valued cross-cleared comparison test `a₁·d₂ + b₂·d₁ ≤ a₂·d₁ + b₁·d₂`, applied to
`t = pair c₁ c₂`. -/
def ratLeCode (t : ℕ) : ℕ :=
  let c1 := t.unpair.1; let c2 := t.unpair.2
  isZero ((qNumP c1 * qDen c2 + qNumN c2 * qDen c1) -
    (qNumP c2 * qDen c1 + qNumN c1 * qDen c2))

end DomainTheory.NeighbourhoodSystems
