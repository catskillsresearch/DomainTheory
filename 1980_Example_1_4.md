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

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Token.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/Token.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/bot_lt_elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem00_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem01_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem10_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11_maximal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elem11_maximal.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemOne_lt_elem11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/elemZero_lt_elem01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/element_classification.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/element_classification.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/eq_of_master_subset.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/eq_of_master_subset.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/inter_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf00_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf01_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf10_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/leaf11_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_inter_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/left_subset_cases.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/master_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/memSet.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/memSet.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_master.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_master.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/mem_right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/not_mem_empty.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/not_mem_empty.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf00.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf00.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf01.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf01.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf10.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf10.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf11.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_leaf11.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_left.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_inter_left.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_subset_cases.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Example14/right_subset_cases.lean)
