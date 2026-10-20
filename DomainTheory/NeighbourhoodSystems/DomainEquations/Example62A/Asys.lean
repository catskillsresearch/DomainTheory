module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

/-- **Scott's domain `A`** packaged as a neighbourhood system over `{0,1}*` (needs `0 < n`). -/
def Asys (n : ℕ) (hn : 0 < n) : NeighborhoodSystem Str where
  mem := MemA n
  master := Set.univ
  master_nonempty := ⟨[], Set.mem_univ _⟩
  master_mem := MemA.univ
  inter_mem := fun hX hY hZ hsub => memA_inter hn hX hY hZ hsub
  sub_master := fun _ => Set.subset_univ _

end Example62A

end DomainTheory.NeighbourhoodSystems
