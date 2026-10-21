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

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12.lean](../Example12.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/Token.lean](Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot.lean](bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_is_unique_partial.lean](bot_is_unique_partial.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemOne.lean](bot_lt_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/bot_lt_elemZero.lean](bot_lt_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemOne.lean](elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/elemZero.lean](elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/element_classification.lean](element_classification.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_bot_of_le_elemZero_of_le_elemOne.lean](eq_bot_of_le_elemZero_of_le_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/eq_of_master_subset.lean](eq_of_master_subset.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_eq.lean](inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/inter_master.lean](inter_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master.lean](master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_inter.lean](master_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_one.lean](master_not_subset_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/master_not_subset_zero.lean](master_not_subset_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem.lean](mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/memSet.lean](memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_iff.lean](mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_master.lean](mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_one.lean](mem_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/mem_zero.lean](mem_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/neighborhoodSystem.lean](neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemOne_le_elemZero.lean](not_elemOne_le_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_elemZero_le_elemOne.lean](not_elemZero_le_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/not_mem_empty.lean](not_mem_empty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one.lean](one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_inter_zero.lean](one_inter_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/one_not_subset_zero.lean](one_not_subset_zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero.lean](zero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_inter_one.lean](zero_inter_one.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example12/zero_not_subset_one.lean](zero_not_subset_one.lean)
