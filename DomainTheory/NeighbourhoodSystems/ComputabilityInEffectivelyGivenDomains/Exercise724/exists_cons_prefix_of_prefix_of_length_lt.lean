/-ai
If a list is a strict prefix of a longer list, then some one-element extension of the shorter list is still a prefix of the longer list.

Write the longer list as the shorter list followed by a remainder. The length hypothesis makes the remainder nonempty, and the head of that remainder is the required element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- If `l ++ [i] <+: l'` fails for every `i`, then... (helper): a list strictly longer than a
prefix of it extends by *some* single element first. -/
theorem exists_cons_prefix_of_prefix_of_length_lt {l l' : List ℕ} (h : l <+: l')
    (hlt : l.length < l'.length) : ∃ i, l ++ [i] <+: l' := by
  obtain ⟨r, hr⟩ := h
  cases r with
  | nil => simp [← hr] at hlt
  | cons i r' => exact ⟨i, r', by rw [← hr]; simp⟩

end DomainTheory.NeighbourhoodSystems.Exercise724
