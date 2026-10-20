module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sierpinski
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `openOfMap f = {x ∣ f(x) = ⊤} = ⋃ {[X] ∣ X f ∅}`: the points sent by `f` to the top of `𝒪`. -/
def openOfMap (f : ApproximableMap V sierpinski) : Set V.Element :=
  {x | ∃ X, x.mem X ∧ f.rel X ∅}

end DomainTheory.NeighbourhoodSystems.Exercise325
