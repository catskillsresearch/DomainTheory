/-ai
A language lies in Scott's family when it is the set of all binary words, a singleton, the concatenation of two languages already in the family, or a nonempty intersection of two languages already in the family.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.concat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- **Scott's family `S`**, as the least fixed point (an inductive predicate). A language `X` is *in
`S`* iff it is built from the four generators:

* `Σ = {0,1}*` itself (`Set.univ`);
* a singleton `{σ}`;
* a concatenation `XY` of two members;
* a *non-empty* intersection `X ∩ Y` of two members. -/
inductive InS : Set (List Bool) → Prop
  | univ : InS Set.univ
  | singleton (σ : List Bool) : InS {σ}
  | mul {X Y : Set (List Bool)} : InS X → InS Y → InS (concat X Y)
  | inter {X Y : Set (List Bool)} : InS X → InS Y → (X ∩ Y).Nonempty → InS (X ∩ Y)

end Exercise722
end DomainTheory.NeighbourhoodSystems
