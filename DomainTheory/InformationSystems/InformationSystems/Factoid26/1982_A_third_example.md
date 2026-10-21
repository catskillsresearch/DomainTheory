# A third example

**A third example.** Let $A$ and $B$ be two fixed sets, and let $D$ as a set consist of the ordered pairs $(a, b)$, with $a \in A$ and $b \in B$, plus the extra object $\Delta$. Here the “information” contained in $(a, b)$ is that $a$ is mapped to $b$ by a yet-to-be-determined function. With this thought in mind, we will know that a finite set of data objects is consistent just in case it is possible that they can all belong to the same function. Formally, we can assert:

$$\{(a_0, b_0), \dots, (a_{k-1}, b_{k-1})\} \in \mathrm{Con} \text{ iff for all } i, j < k \text{ whenever } a_i = a_j, \text{ then } b_i = b_j.$$

It is something of a bother having to throw in $\Delta$ in this case, but all we have to say is that if $u$ is consistent under the above rule, then so also will $u \cup \{\Delta\}$; and these are the only consistent sets of data objects for this example. Perhaps it would make more sense to use $\{(a, b)\}$ in place of the simpler $(a, b)$, and then we could set $\Delta = \emptyset$ more naturally. From this point of view we can regard each data object as a (very small!) fragment of the graph of a function; the consistent sets then point to larger fragments of graphs.

The definition of the entailment relation is the minimal one:

$$u \vdash X \text{ iff either } X = \Delta \text{ or } X \in u.$$

These examples show that sometimes the main part of the structure is in $\mathrm{Con}$, sometimes it is in $\vdash$, and sometimes it is in the interplay between the two notions. The object $\Delta$ is not in itself very important, but it is sometimes useful to have an object there that can always be counted upon to act in the same way in every system. ■

**Lean 4**

- [InformationSystems/InformationSystems/Factoid26.lean](../Factoid26.lean)
- [InformationSystems/InformationSystems/Factoid26/Basic.lean](Basic.lean)
- [InformationSystems/InformationSystems/Factoid26/Consistent.lean](Consistent.lean)
- [InformationSystems/InformationSystems/Factoid26/Ent.lean](Ent.lean)
- [InformationSystems/InformationSystems/Factoid26/Token.lean](Token.lean)
- [InformationSystems/InformationSystems/Factoid26/consistent_empty.lean](consistent_empty.lean)
- [InformationSystems/InformationSystems/Factoid26/consistent_insert_bot.lean](consistent_insert_bot.lean)
- [InformationSystems/InformationSystems/Factoid26/consistent_insert_mem.lean](consistent_insert_mem.lean)
- [InformationSystems/InformationSystems/Factoid26/consistent_singleton.lean](consistent_singleton.lean)
- [InformationSystems/InformationSystems/Factoid26/consistent_subset.lean](consistent_subset.lean)
- [InformationSystems/InformationSystems/Factoid26/partialFunctionSystem.lean](partialFunctionSystem.lean)
