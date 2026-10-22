module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.V_noMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.U_isPositive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.U_noMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.U_diffClosed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.splitFromBisection_isSplitSpecu27
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


/-- **`8.12(g)(3)`, `U`-as-prober half**: `splitX812e` also satisfies `SplitSpec'` — completing the
concrete-construction half of `8.12(g)(3)` left open by `Exercise812e.lean`'s generic
`splitFromBisection_isSplitSpec'`. The extra hypothesis it needs, `∀ j, VX j ≠ ∅`, is immediate:
every `VX j` is `V.mem`-genuine (`VComputablePresentation.mem_X`) and `V.mem` structurally excludes
`∅` (`V.mem X := ∃ k m, X = levelSet k m ∧ X.Nonempty`, `Exercise812.lean` line 199). -/
theorem hxSplit812e : SplitSpec' V splitX812e :=
  ComputableBisection.splitFromBisection_isSplitSpec' UComputablePresentation U_isComputableDiff
    B812e V_noMinimal U_isPositive U_noMinimal U_diffClosed (fun j => (VX_nonempty j).ne_empty)

end DomainTheory.NeighbourhoodSystems
