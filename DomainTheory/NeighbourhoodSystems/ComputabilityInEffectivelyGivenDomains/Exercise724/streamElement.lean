/-ai
The element of the domain of L determined by an infinite sequence is the filter of neighbourhoods that contain the neighbourhood of some finite prefix of the sequence. A member is a neighbourhood of L containing some prefix neighbourhood. The master neighbourhood is the neighbourhood of the empty prefix. The intersection of two members contains the prefix neighbourhood of the longer index, because prefix neighbourhoods shrink as the index grows. A neighbourhood containing a member contains the same prefix neighbourhood.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_finPrefix_antitone

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **The element of `|L|` determined by an infinite sequence `f`**: the filter of neighbourhoods
containing some finite prefix of `f` — Scott's `limitFamily` (Definition 1.6's motivating prose),
specialized to `L`'s prefix chain `nbhd (finPrefix f ·)`. -/
def streamElement (f : ℕ → ℕ) : L.Element where
  mem Z := L.mem Z ∧ ∃ n, nbhd (finPrefix f n) ⊆ Z
  sub h := h.1
  master_mem := ⟨mem_nbhd [], 0, subset_rfl⟩
  inter_mem := by
    rintro X Y ⟨hXmem, n, hXsub⟩ ⟨hYmem, m, hYsub⟩
    have hn : nbhd (finPrefix f (max n m)) ⊆ X :=
      (nbhd_finPrefix_antitone f (le_max_left n m)).trans hXsub
    have hm : nbhd (finPrefix f (max n m)) ⊆ Y :=
      (nbhd_finPrefix_antitone f (le_max_right n m)).trans hYsub
    exact ⟨L.inter_mem hXmem hYmem (mem_nbhd _) (Set.subset_inter hn hm),
      max n m, Set.subset_inter hn hm⟩
  up_mem := by
    rintro X Y ⟨-, n, hn⟩ hYmem hXY
    exact ⟨hYmem, n, hn.trans hXY⟩

end DomainTheory.NeighbourhoodSystems.Exercise724
