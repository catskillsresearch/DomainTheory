/-ai
In the sharp presentation built from a computable presentation of D, the neighbourhood enumerated at an index is the sharp neighbourhood of that index.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

@[simp] theorem dsharpPresentation_X (P : ComputablePresentation D) (n : ℕ) :
    (dsharpPresentation P hD).X n = Vsharp D P n := rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
