module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

@[simp] theorem dsharpPresentation_X (P : ComputablePresentation D) (n : ℕ) :
    (dsharpPresentation P hD).X n = Vsharp D P n := rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
