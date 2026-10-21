/-ai
The one-neighbourhood system on a nonempty set of binary words has that set as its only neighbourhood and as its master. The intersection of the neighbourhood with itself is the set, every neighbourhood equals the master, and the system is free of the empty set because the set is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.ScottSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpr

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **The one-neighbourhood system `{Γ}`** over `{0,1}*`: its only neighbourhood is `Γ` itself, and
its master (token set) is `Γ`. It is `∅`-free precisely because `Γ` is non-empty. -/
def singletonSys (Γ : Set Str) (h : Γ.Nonempty) : ScottSys where
  sys :=
    { mem := fun X => X = Γ
      master := Γ
      master_nonempty := h
      master_mem := rfl
      inter_mem := by
        intro X Y Z hX hY _ _
        show X ∩ Y = Γ
        rw [hX, hY, Set.inter_self]
      sub_master := by intro X hX; rw [show X = Γ from hX] }
  ne := by intro X hX; rw [show X = Γ from hX]; exact h

end Exercise619

end DomainTheory.NeighbourhoodSystems
