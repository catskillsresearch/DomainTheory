module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- **`x^§|_{↑X} = ↑(0X)`**: `inSharp` sends the principal element `↑X` to the principal element of
the leaf neighbourhood `0X`. -/
theorem inSharp_principal {X : Set α} (hX : D.mem X) :
    inSharp D hD (D.principal hX) = (Dsharp D hD).principal (MemS.zero hX) := by
  rw [← inSharpMap_toElementMap hD]
  apply Element.ext
  intro W
  simp only [mem_principal, ← rel_iff_mem_principal (inSharpMap hD) hX, inSharpMap_rel]
  exact ⟨fun h => h.2, fun h => ⟨hX, h⟩⟩

end DomainTheory.NeighbourhoodSystems
