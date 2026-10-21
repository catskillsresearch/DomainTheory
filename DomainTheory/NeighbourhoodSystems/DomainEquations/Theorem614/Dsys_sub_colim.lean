/-ai
Each level of the tower is a subdomain of the colimit.

The masters agree by the master computations for the colimit and for the tower. A neighbourhood of the level is a neighbourhood of the colimit at that index. For the consistency clause, a neighbourhood of an intersection that lives at some level is moved by the chain inclusion into the maximum of the two indices, and the chain inclusion of the original level into that maximum supplies the inherited consistency.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.chain_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- Each level of the tower is a subdomain of the colimit: `Tⁿ({Γ}) ◁ 𝒟`. -/
theorem Dsys_sub_colim (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ colim s where
  master_eq := by rw [colim_master, Dsys_master]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (Dsys s (max n m)).mem (X ∩ Y) := by
      have hle : (Dsys s m) ◁ (Dsys s (max n m)) := chain_le s (le_max_right n m)
      exact hle.sub hXY
    -- pull `X ∩ Y` back into `Tⁿ({Γ})` using consistency-in-the-bigger-level
    exact (chain_le s (le_max_left n m)).inter_closed hX hY hN

end Theorem614

end DomainTheory.NeighbourhoodSystems
