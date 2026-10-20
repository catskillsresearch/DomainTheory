module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419








/-- `⊥ = []⊥` in `C` (the cone of `Λ` is the master). -/
theorem strBot_nil : strBot [] = C.bot := by
  apply Element.ext
  intro Y
  rw [strBot, mem_principal, mem_bot, cone_nil, C_master]
  exact ⟨fun h => Set.Subset.antisymm (Set.subset_univ _) h.2,
    fun h => ⟨h ▸ C.master_mem, h ▸ Set.Subset.refl _⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
