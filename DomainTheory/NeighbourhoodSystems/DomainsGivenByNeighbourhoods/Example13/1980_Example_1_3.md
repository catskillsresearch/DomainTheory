# Example 1.3

EXAMPLE 1.3. Let $\Delta = \{0, 1, 2\}$ and let $\mathcal{D} = \{\{0, 1, 2\}, \{1, 2\}, \{2\}\}$.

In pictures we have:

```
╭──────────────────────────────────────╮
│  0   ╭──────────────────────╮        │
│      │  1        ╭───╮       │        │
│      │           │ 2 │       │        │
│      │           ╰───╯       │        │
│      ╰──────────────────────╯        │
╰──────────────────────────────────────╯
Instead of stepping to the total element (here represented by 2) in one big step, the passage is divided into two steps. (Note 0 and 1 cannot be taken as representing total elements.) This example is not very interesting because the direction of approximation is unique. We need an example with some choice. $\square$

**Lean 4**

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/Token.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/bot_lt_elemTwelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/bot_lt_elemTwelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwelve_lt_elemTwo.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwelve_lt_elemTwo.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwo.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwo.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwo_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/elemTwo_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/element_classification.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/element_classification.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/eq_of_master_subset.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/eq_of_master_subset.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/inter_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/inter_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/inter_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_not_subset_twelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_not_subset_twelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_not_subset_two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/master_not_subset_two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/memSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_twelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_twelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/mem_two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve_inter_two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve_inter_two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve_not_subset_two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/twelve_not_subset_two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/two.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/two.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/two_inter_twelve.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example13/two_inter_twelve.lean)
