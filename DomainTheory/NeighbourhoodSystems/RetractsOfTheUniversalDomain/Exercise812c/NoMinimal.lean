/-ai
A neighbourhood system is atomless when every neighbourhood splits into two disjoint nonempty neighbourhoods whose union is the original set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Atomlessness** ("no minimal neighbourhoods"), generalizing `U_no_minimal`/`V_no_minimal`:
every non-empty neighbourhood splits into two disjoint, non-empty neighbourhood pieces whose union
recovers it. (Phrased with explicit `Nonempty` clauses, equivalent given `Y ∩ Z = ∅`/`Y ∪ Z = X` to
`U_no_minimal`/`V_no_minimal`'s own `Y ≠ X`/`Z ≠ X` phrasing, but directly what `exists_split'`
needs — an *abstract* `D.mem` need not itself carry nonemptiness the way `U.mem`/`V.mem` do.) -/
def NeighborhoodSystem.NoMinimal {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X : Set α}, D.mem X →
    ∃ Y Z : Set α, D.mem Y ∧ D.mem Z ∧ Y.Nonempty ∧ Z.Nonempty ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X

end DomainTheory.NeighbourhoodSystems
