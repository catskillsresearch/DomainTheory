# Exercise 1.12

In words, the intersection is the best element that is at the same time an approximation to all of the elements $x_n$; the intersection is exactly what is common to all the given elements. The union on the other hand is just what the (increas-
The union on the other hand is just what the (increasing sequence of the) $x_n$ approximates; the union combines contributions from all the $x_n$ into a "better" element -- but no more than that.

In thinking about domains a rough diagram of the partial-ordering relation $\subseteq$ between elements is often helpful. The picture of 1.4 is an example where the nodes represent the elements. Any finite tree growing up from a root node would also be an example. Indeed, any finite partially ordered set with least element would be an example. (Here no distinction between tokens and elements is necessary.) A lattice diagram is also illustrated.

**A TREE**

```
        ○
       ╱ ╲
      ○   ○
     ╱│╲ ╱│
    ○ ○ ○ ○
     ╲│╱ ╲│
      ○   ○
       ╲ ╱
        ○
        ⊥
```

**A ROUGH PICTURE**

```
   ∿∿∿∿∿∿∿∿∿∿∿
  ╱ │ │ │ │ ╲
 ╱  │ │ │ │  ╲
╱   │ │ │ │   ╲
╲   │ │ │ │   ╱
 ╲  │ │ │ │  ╱
  ╲ │ │ │ │ ╱
   ╲│ │ │ │╱
    ○
    ⊥
```

**A LATTICE**

```
       ○
      ╱│╲
     ╱ │ ╲
    ○  ○  ○
    │╲ │ ╱│
    │ ╲│╱ │
    ○  ○  ○
     ╲ │ ╱
      ╲│╱
       ○
       ⊥
```

The root node is the element $\perp$ of $|\mathcal{D}|$; there need be no top node $\top$. *Approximation* is represented by a passage from a lower node to a higher node along the rising lines. The system $\mathcal{D}$ of neighbourhoods is the collection of sets each of which is all
the nodes above a given node. For infinite examples, however, care must be given to introduce limit nodes. The first few exercises should be provided with pictures to illustrate the structure.

## EXERCISES

**EXERCISE 1.12.** Let $\Delta = \mathbb{N} = \{0, 1, 2, \ldots, n, \ldots\}$ be the set of non-negative integers. Use as neighbourhoods final segments:

$$
\{m \in \mathbb{N} \mid m > n\}
$$

for $n \in \mathbb{N}$. Verify that this is a neighbourhood system. What are the total elements? What are the finite elements? Draw a picture of the approximation relation in this domain. (Hint: there is only one limit element.)

**Lean 4**

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/element_eq.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/element_eq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin_le_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin_le_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin_strictMono.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/fin_strictMono.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/isTotal_iff_top.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/isTotal_iff_top.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/le_top.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/le_top.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem_tail.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem_tail.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem_tail_nbhd.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/mem_tail_nbhd.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/neighborhoodSystem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/neighborhoodSystem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/nestedOrDisjoint.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/nestedOrDisjoint.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/ns_mem.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/ns_mem.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail_inter.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail_inter.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail_subset_iff.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/tail_subset_iff.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/top.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/top.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/top_isTotal.lean](DomainTheory/NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise112/top_isTotal.lean)
