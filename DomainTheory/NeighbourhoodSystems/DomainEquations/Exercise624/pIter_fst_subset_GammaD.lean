/-ai
The first component of each stage of the pair iteration is included in the colimit Gamma_D.

A member of the m-th first component lies in the union at index m.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- Each stage sits inside the colimit `Γ_D` (choice-free; avoids `Set.subset_iUnion`). -/
theorem pIter_fst_subset_GammaD (m : ℕ) : (pIter m).1 ⊆ GammaD :=
  fun _ hx => Set.mem_iUnion.mpr ⟨m, hx⟩

end Exercise624
end DomainTheory.NeighbourhoodSystems
