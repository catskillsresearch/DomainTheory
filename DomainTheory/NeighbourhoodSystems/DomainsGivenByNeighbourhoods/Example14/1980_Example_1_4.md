# Example 1.4

EXAMPLE 1.4. Let $\Delta = \{\Lambda, 0, 1, 00, 01, 10, 11\}$ and let $\mathcal{D} = \{\Delta, \{0, 00, 01\}, \{1, 10, 11\}, \{00\}, \{01\}, \{10\}, \{11\}\}$.

Or more understandably in pictures:

```
╭──────────────────────────────────────────────────────────────╮
│   ╭───╮      ╭───╮      ╭───╮      ╭───╮                     │
│   │00 │      │01 │      │10 │      │11 │                     │
│   ╰───╯      ╰───╯      ╰───╯      ╰───╯                     │
│     ╭──────────────────╮    ╭──────────────────╮             │
│     │ 0    00     01   │    │ 1    10     11   │             │
│     ╰──────────────────╯    ╰──────────────────╯             │
│          ╭──────────╮              ╭──────────╮              │
│          │    0     │              │    1     │              │
│          ╰──────────╯              ╰──────────╯              │
│                 ╭──────────────────────────╮                 │
│                 │            Λ             │                 │
│                 ╰──────────────────────────╯                 │
╰──────────────────────────────────────────────────────────────╯
```

The tokens are finite sequences of 0's and 1's (up to length 2) with $\Lambda$ the empty sequence; they form — in the picture — the binary tree with the sequences as the nodes. The neighbourhoods are the subtrees of all nodes above a given node. Obviously this can be generalized to sequences of any length (and to trees less regular than the binary tree). The total elements of the example correspond to the top nodes 00, 01, 10, 11 and the lower nodes to the partial elements. When we are not at a top node we have only partially determined a sequence, and the branching indicates that we have some choice as to how the sequence can be extended. $\square$

It should be noted that, in these three examples, the reason that we have a neighbourhood system is a simple consequence of a

**Resolutions from the image:** “is unique” (not “in unique”); $\mathcal{D}$ begins with $\Delta$, not $\Lambda$; Pass 1’s nested-box diagram matches the neighborhood boundaries in the scan; em dashes around “in the picture” as in the source.
very special circumstance: in these systems two neighbourhoods are either disjoint or one is included in the other. This arrangement of neighbourhoods is by no means necessary.

**Lean 4**

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Token.lean](Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00.lean](leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01.lean](leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf01.lean](leaf00_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf00.lean](leaf01_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10.lean](leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf10.lean](leaf00_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf10.lean](leaf01_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf00.lean](leaf10_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf01.lean](leaf10_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11.lean](leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf11.lean](leaf00_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf11.lean](leaf01_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf11.lean](leaf10_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf00.lean](leaf11_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf01.lean](leaf11_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf10.lean](leaf11_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left.lean](left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf00.lean](left_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_left.lean](leaf00_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf01.lean](left_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_left.lean](leaf01_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf10.lean](left_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_left.lean](leaf10_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf11.lean](left_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_left.lean](leaf11_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master.lean](master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_master.lean](inter_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master_inter.lean](master_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right.lean](right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_right.lean](left_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/memSet.lean](memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem.lean](mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf00.lean](mem_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf01.lean](mem_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf10.lean](mem_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf11.lean](mem_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_left.lean](mem_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_master.lean](mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_right.lean](mem_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_iff.lean](mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/eq_of_master_subset.lean](eq_of_master_subset.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_subset_cases.lean](leaf00_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_subset_cases.lean](leaf01_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_subset_cases.lean](leaf10_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_subset_cases.lean](leaf11_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_subset_cases.lean](left_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/not_mem_empty.lean](not_mem_empty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf00.lean](right_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_right.lean](leaf00_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf01.lean](right_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_right.lean](leaf01_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf10.lean](right_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_right.lean](leaf10_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf11.lean](right_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_right.lean](leaf11_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_left.lean](right_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_eq.lean](inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/neighborhoodSystem.lean](neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot.lean](bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00.lean](elem00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01.lean](elem01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero.lean](elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_subset_cases.lean](right_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10.lean](elem10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11.lean](elem11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne.lean](elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemOne.lean](bot_lt_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemZero.lean](bot_lt_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00_maximal.lean](elem00_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01_maximal.lean](elem01_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10_maximal.lean](elem10_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11_maximal.lean](elem11_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem10.lean](elemOne_lt_elem10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem11.lean](elemOne_lt_elem11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem00.lean](elemZero_lt_elem00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem01.lean](elemZero_lt_elem01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/element_classification.lean](element_classification.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14.lean](../Example14.lean)
