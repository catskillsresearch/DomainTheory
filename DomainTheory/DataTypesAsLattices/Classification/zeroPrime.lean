/-ai
Scott's auxiliary value 0′, used in the many-valued tables of Theorem 6.7, is the union of the singletons {0} and {1}. The transcribed equation 0′ = 0 ∪ ⊥ equals 0 and would collapse the tables, so the point distinct from ⊥, 0, and ⊤ is taken to be {0, 1}.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Scott's auxiliary value `0'` used in the many-valued tables of Theorem 6.7.
    The vision transcription writes `0' = 0 ∪ ⊥`, which equals `0` and would
    collapse the tables; the tables need a point distinct from `⊥`, `0`, and
    `⊤`, so we take `0 ∪ 1`. -/
def zeroPrime : Pomega := ofNat 0 ∪ ofNat 1

end DomainTheory.DataTypesAsLattices
