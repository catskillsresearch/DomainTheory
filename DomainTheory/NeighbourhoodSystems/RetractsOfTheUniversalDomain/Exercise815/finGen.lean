/-ai
The finitely generated subsystem on a finite index list is the set of neighbourhoods that arise as the partial meet, starting from the master neighbourhood, of some sublist of that list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

/-- **`Fin(js)`**: the finitely generated subsystem of `D` on the index list `js` — the set of
`D`-consistent "sub-meets" `interFrom P D.master sub` for sublists `sub ⊑ js`. Every member is
automatically a `D`-neighbourhood (the `D.mem Y` conjunct), so `finGen P js ⊆ D.mem` by
construction. -/
def finGen (js : List ℕ) : Set (Set α) :=
  {Y | ∃ sub : List ℕ, sub.Sublist js ∧ D.mem Y ∧ Y = interFrom P D.master sub}

end FinGen

end DomainTheory.NeighbourhoodSystems
