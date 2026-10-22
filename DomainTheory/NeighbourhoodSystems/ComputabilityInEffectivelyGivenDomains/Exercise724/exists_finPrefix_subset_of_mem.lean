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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_length
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.HasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toStream
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd_finPrefix_toStream

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **Every neighbourhood `Z ∈ x` contains some sufficiently deep prefix.** `Z = nbhd l` for some
`l` (`x.sub`), and comparing `nbhd l` against the (unboundedly long) chain
`nbhd (finPrefix (toStream x hx) n)` — nested, not disjoint, by the same
`x.inter_mem`/`L_nestedOrDisjoint` argument as `exists_extend_of_not_hasMin` — forces `l` itself to
be a prefix of the chain once `n > l.length` (the chain entry is then too long to be *the* shorter
side). Together with `mem_nbhd_finPrefix_toStream` this gives `streamElement (toStream x hx) = x`
(used directly in `toElement_surjective`). -/
theorem exists_finPrefix_subset_of_mem (x : L.Element) (hx : ¬ HasMin x) {Z : Set Gamma}
    (hZ : x.mem Z) : ∃ n, nbhd (finPrefix (toStream x hx) n) ⊆ Z := by
  obtain ⟨l, rfl⟩ := x.sub hZ
  refine ⟨l.length + 1, ?_⟩
  set n := l.length + 1
  have hn : x.mem (nbhd (finPrefix (toStream x hx) n)) := mem_nbhd_finPrefix_toStream x hx n
  have hinter := x.inter_mem hZ hn
  rcases L_nestedOrDisjoint (mem_nbhd l) (mem_nbhd (finPrefix (toStream x hx) n)) with
    hsub | hsub | hdisj
  · -- nbhd l ⊆ nbhd (finPrefix _ n): impossible by length once n = l.length + 1
    have hpre : finPrefix (toStream x hx) n <+: l := (nbhd_subset_iff l _).mp hsub
    have := hpre.length_le
    rw [finPrefix_length] at this
    omega
  · exact hsub
  · exfalso
    rw [hdisj] at hinter
    obtain ⟨l', hl'⟩ := x.sub hinter
    exact (nbhd_nonempty l').ne_empty hl'.symm

end DomainTheory.NeighbourhoodSystems.Exercise724
