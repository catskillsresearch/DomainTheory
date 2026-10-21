/-ai
The power-domain action of a map relates neighbourhoods A and B exactly when both are power-domain neighbourhoods and every member of A is related by the map to some member of B.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}

@[simp] theorem PFmap_rel {f : ApproximableMap V W} {A : Set (Set α)} {B : Set (Set β)} :
    (PFmap f).rel A B ↔ V.PDmem A ∧ W.PDmem B ∧ ∀ X ∈ A, ∃ Y ∈ B, f.rel X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
