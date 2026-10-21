/-ai
The denotation of the safe active decode of any index is nonempty.

If decoding fails, the safe decode is sigma and its denotation is the whole set of tokens. If decoding succeeds and the nonemptiness decision holds, the safe decode is that expression and the decision supplies a nonempty denotation. If the decision fails, the safe decode is again sigma.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem safeDecodeActive_nonempty (n : ℕ) : (denote (safeDecodeActive n)).Nonempty := by
  unfold safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => exact Set.univ_nonempty
  | some e =>
    by_cases hb : decideNonemptyB e = true
    · simp [hb]; exact (decideNonemptyB_iff e).mp hb
    · simp [hb, denote_sigma]

end Exercise722

end DomainTheory.NeighbourhoodSystems
