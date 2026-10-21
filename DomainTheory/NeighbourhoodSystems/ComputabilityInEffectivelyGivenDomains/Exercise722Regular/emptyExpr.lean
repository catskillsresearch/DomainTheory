/-ai
emptyExpr is the expression for the empty language, the intersection of the singleton of the bit zero with the singleton of the bit one. It is the canonical empty expression used to phrase emptiness as an equivalence of languages.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst16
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst17

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- The empty language is denotable in the fragment (it is **not** a member of `S`, which is
positive): `{0} ∩ {1} = ∅`. This is the canonical "`∅`" expression used to phrase emptiness as an
equivalence query. -/
def emptyExpr : SExpr := .cap (.single [false]) (.single [true])

end Exercise722

end DomainTheory.NeighbourhoodSystems
