/-ai
The enumeration of Definition 7.1 sends an index to the denotation of the S-expression decoded from that index when the denotation is decided nonempty, and otherwise, including on codes that do not decode, to the default neighbourhood, the set of all bit lists. Every index therefore names a member of the positive system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_default

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- **Definition 7.1 enumeration backbone.** Decode `n` to an `SExpr`; if the denotation is
non-empty (`decideNonemptyB`), use it; otherwise (or on junk codes) use `Σ` so every index names a
member of the positive system `S`. -/
def SsysX (n : ℕ) : Set (List Bool) :=
  match SExpr.decode n with
  | none => SsysX_default
  | some e =>
    if decideNonemptyB e then denote e else SsysX_default

end Exercise722

end DomainTheory.NeighbourhoodSystems
