/-ai
The pairing constructor sends the pair of the principal elements of two tree neighbourhoods to the principal element of the corresponding node neighbourhood.

Rewrite pairing as the pairing map applied to the principal element of the product neighbourhood, and compare membership. A pairing relation decomposes into membership of the node and containment of the product of the two neighbourhoods, which is membership in that principal element, and conversely.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.pair_principal_eq_principal_prodNbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- **`⟨↑P, ↑Q⟩^§ = ↑(1P∪2Q)`**: `pairSharp` sends a pair of principal elements to the principal
element of the corresponding node neighbourhood. -/
theorem pairSharp_principal {P Q : Set (List Bool × α)} (hP : MemS D P) (hQ : MemS D Q) :
    pairSharp D hD ((Dsharp D hD).principal hP) ((Dsharp D hD).principal hQ)
      = (Dsharp D hD).principal (MemS.pair hP hQ) := by
  rw [← pairSharpMap_toElementMap hD, pair_principal_eq_principal_prodNbhd hP hQ]
  apply Element.ext
  intro W
  rw [mem_principal, ← rel_iff_mem_principal (pairSharpMap hD) (prod_mem_prodNbhd hP hQ),
    pairSharpMap_rel]
  constructor
  · rintro ⟨-, hW, A, B, hA, hB, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hW, hsub⟩
  · rintro ⟨hW, hsub⟩
    exact ⟨prod_mem_prodNbhd hP hQ, hW, P, Q, hP, hQ, rfl, hsub⟩

end DomainTheory.NeighbourhoodSystems
