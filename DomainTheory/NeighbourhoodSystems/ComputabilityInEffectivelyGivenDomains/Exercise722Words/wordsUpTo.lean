/-ai
The list wordsUpTo n enumerates every word over the two Boolean letters of length at most n, without duplicates. At zero it is the singleton list containing the empty word. At a successor it appends, to the previous list, the flattening of each earlier word w into the two extensions by false and by true.
ai-/
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
