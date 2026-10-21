/-ai
U has a computable difference. The index is the canonical difference code, which is primitive recursive, presents the difference whenever that difference is a neighbourhood, and for which presentability of a difference is recursively decidable.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.U_diff_computable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`U` has a computable `\`**, completing the missing prerequisite this section opened with. -/
def U_isComputableDiff : IsComputableDiff UComputablePresentation where
  diffIdx := Udiff
  diffIdx_primrec := Udiff_primrec
  diffIdx_spec := Udiff_spec
  diff_computable := U_diff_computable

end DomainTheory.NeighbourhoodSystems
