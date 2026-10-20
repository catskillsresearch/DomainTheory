module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- Every word over `{false,true}` of length at most `n`, listed without duplicates. -/
def wordsUpTo : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    (wordsUpTo n) ++ (wordsUpTo n).flatMap fun w => [[false] ++ w, [true] ++ w]

end Exercise722

end DomainTheory.NeighbourhoodSystems
