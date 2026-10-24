module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Dsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Esol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Fsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Gsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaE

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- Each stage sits inside the colimit `Γ_E` (choice-free). -/
theorem pIter_snd_subset_GammaE (m : ℕ) : (pIter m).2 ⊆ GammaE :=
  fun _ hx => Set.mem_iUnion.mpr ⟨m, hx⟩

end Exercise624
end DomainTheory.NeighbourhoodSystems
