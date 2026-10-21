# Definition 8.7

These results have almost completely translated the theory of $\triangleleft$-subdomains into $\lambda$-calculus via the sub-combinator. One last step will complete the passage, and then we shall be able to return to solving domain equations.

**DEFINITION 8.7.** Let $\mathbb{Q}$ be the set of rational numbers, and let
$$[0, 1) = \{q \in \mathbb{Q} \mid 0 \le q < 1\},$$
and similarly for $[r, s)$ for any $r < s$ in $\mathbb{Q}$. The neighbourhood system $\mathcal{U}$ over $[0, 1)$ is the set of all non-empty finite unions of rational intervals $[r, s)$ with $0 \le r < s \le 1$. $\square$

A picture of a typical element of $\mathcal{U}$ could be drawn like this:

```
0    r_0  r_1     r_2  r_3     r_4  r_5     1
[======)       [=====)       [=====)
```

Note that any union can be taken as a *disjoint* union of the form
$$\bigcup_{i \le n} [r_{2i}, r_{2i+1})$$
where $0 \le r_0 < r_1 < r_2 < \cdots < r_{2n} < r_{2n+1} \le 1$. (Hint: Any overlapping intervals or abutting intervals can always be combined into one long interval.) It is a most elementary exercise to show that, by virtue of this representation, the system $\mathcal{U}$ has a computable presentation. (Some isomorphic versions of $\mathcal{U}$ — equally effective — are recorded in the exercises.) Note that $\mathcal{U}$ has no minimal neighbourhoods: every set in $\mathcal{U}$ can be written as the union of two disjoint sets in $\mathcal{U}$. (Hint: Use the density of the ordering of $\mathbb{Q}$.) The significance of $\mathcal{U}$ can now be explained.

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87.lean](../Definition87.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/U.lean](U.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/UMaster.lean](UMaster.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/UMaster_nonempty.lean](UMaster_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/UMem.lean](UMem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/U_iUnion_mem.lean](U_iUnion_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/U_inter_mem.lean](U_inter_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/U_master_mem.lean](U_master_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/U_no_minimal.lean](U_no_minimal.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/U_sub_master.lean](U_sub_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/U_union_mem.lean](U_union_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/clip.lean](clip.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/clipGe.lean](clipGe.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/clipLt.lean](clipLt.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/combineIntervals.lean](combineIntervals.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/mem_presentedIntervals.lean](mem_presentedIntervals.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/presentedIntervals.lean](presentedIntervals.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/presentedIntervals_append.lean](presentedIntervals_append.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/presentedIntervals_cons.lean](presentedIntervals_cons.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/presentedIntervals_inter.lean](presentedIntervals_inter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition87/presentedIntervals_nil.lean](presentedIntervals_nil.lean)
