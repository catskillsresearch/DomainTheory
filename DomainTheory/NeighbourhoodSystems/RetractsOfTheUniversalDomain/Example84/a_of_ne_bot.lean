/-ai
The map associated with an element sends every element other than bottom to that chosen element.

Extensionality of elements and the membership criterion of the map give both directions. From a membership in the image, the left alternative rewrites the master membership of the chosen element, and the right alternative is already a membership in the chosen element. From a membership in the chosen element, the law that a neighbourhood of an element is a neighbourhood of the system supplies the first component of the criterion, and the hypothesis that the input differs from bottom supplies the right disjunct.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂


variable {α : Type*} {D : NeighborhoodSystem α}


variable (u : D.Element) (hu : u ≠ D.bot)


theorem a_of_ne_bot {x : D.Element} (hx : x ≠ D.bot) : (a u).toElementMap x = u := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a]
  constructor
  · rintro ⟨-, hZeq | ⟨-, huZ⟩⟩
    · exact hZeq ▸ u.master_mem
    · exact huZ
  · intro huZ
    exact ⟨u.sub huZ, Or.inr ⟨hx, huZ⟩⟩

end DomainTheory.NeighbourhoodSystems
