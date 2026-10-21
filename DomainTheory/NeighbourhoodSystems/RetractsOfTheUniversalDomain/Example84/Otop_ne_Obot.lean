/-ai
The top element of the two-point system is distinct from its bottom element.

If they agreed, the singleton of zero would belong to the bottom and hence equal the master, the full two-point set. One would then belong to the singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂


theorem Otop_ne_Obot : Otop ≠ O.bot := by
  intro h
  have h1 : Otop.mem ({0} : Set (Fin 2)) := ⟨O_mem_zero, subset_rfl⟩
  rw [h, mem_bot, O_master_eq] at h1
  have h2 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := by rw [h1]; simp
  simp at h2

end DomainTheory.NeighbourhoodSystems
