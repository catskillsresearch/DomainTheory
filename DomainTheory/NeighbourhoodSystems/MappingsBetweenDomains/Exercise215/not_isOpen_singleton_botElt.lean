/-ai
The singleton of the bottom element is not an open subset of the domain of O.

If it were open, some neighbourhood of the bottom element would have its basic open contained in the singleton. Membership in the bottom element forces that neighbourhood to be the universe. The top element contains the master neighbourhood, which is the universe, so the top element lies in the basic open and therefore in the singleton. That contradicts the distinctness of the bottom and top elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.botElt_ne_topElt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem
















/-- **The opens of `|𝒪|`.** `{⊥}` is not open: `⊥` is the generic point. (The basic neighbourhood of
`⊥` is `[Δ] = |𝒪|`, which is not contained in `{⊥}` because it also contains `⊤`.) -/
theorem not_isOpen_singleton_botElt : ¬ IsOpen ({botElt} : Set O.Element) := by
  intro h
  obtain ⟨X, hX, hsub⟩ := h botElt rfl
  rw [mem_botElt] at hX
  subst hX
  have htop : topElt ∈ ({botElt} : Set O.Element) :=
    hsub (show topElt ∈ O.basicOpen Set.univ from (O_master ▸ topElt.master_mem))
  exact botElt_ne_topElt (Set.mem_singleton_iff.mp htop).symm

end DomainTheory.NeighbourhoodSystems.Exercise215
