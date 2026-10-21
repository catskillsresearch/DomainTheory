# Example 1.2

EXAMPLE 1.2. Let $\Delta = \{0, 1\}$ and let $\mathcal{D} = \{\{0, 1\}, \{0\}, \{1\}\}$.

In pictures we have:

```
╭──────────────────────────╮
│   ╭───╮       ╭───╮      │
│   │ 0 │       │ 1 │      │
│   ╰───╯       ╰───╯      │
╰──────────────────────────╯
```

The intention is that 0 and 1 can be completely specified and that they can be identified with the total elements. As we shall see, there is only one partial element: either we give no information (the neighbourhood $\{0, 1\}$), or we decide between 0 and 1 (by giving $\{0\}$ or $\{1\}$). $\square$

**Lean 4**

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Token.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_is_unique_partial.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_is_unique_partial.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/element_classification.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/element_classification.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_bot_of_le_elemZero_of_le_elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_bot_of_le_elemZero_of_le_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_of_master_subset.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_of_master_subset.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/memSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemOne_le_elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemOne_le_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemZero_le_elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemZero_le_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_mem_empty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_mem_empty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_inter_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_inter_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_not_subset_zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_not_subset_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_inter_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_inter_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_not_subset_one.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_not_subset_one.lean)
