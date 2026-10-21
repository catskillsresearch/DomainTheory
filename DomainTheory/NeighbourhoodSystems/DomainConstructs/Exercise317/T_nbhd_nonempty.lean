/-ai
Every neighbourhood of the truth system is nonempty.

The membership criterion splits into the master, the zero neighbourhood, and the one neighbourhood, inhabited respectively by the token 0, the token 0, and the token 1.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `T`-neighbourhoods are non-empty (`∅ ∉ T`). -/
theorem T_nbhd_nonempty {F : Set Token} (hF : T.mem F) : F.Nonempty := by
  rcases (Example12.mem_iff F).mp hF with rfl | rfl | rfl
  · exact ⟨0, by simp [Example12.master]⟩
  · exact ⟨0, by simp [Example12.zero]⟩
  · exact ⟨1, by simp [Example12.one]⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
