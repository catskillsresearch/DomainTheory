# Exercise 3.26

**EXERCISE 3.26.** Show that for every domain $D$ there is an approximable mapping

$$\mathrm{cond} : T \times D \times D \to D,$$

called the *conditional operator*, satisfying

(i) $\mathrm{cond}(\mathrm{true}, x, y) = x$

(ii) $\mathrm{cond}(\mathrm{false}, x, y) = y$

(iii) $\mathrm{cond}(\bot, x, y) = \bot$ .

(Hint: Recalling that $T = \{\{0\}, \{1\}, \{0, 1\}\}$, define cond as a relation by

$$
\begin{aligned}
0C \cup 10X \cup 110Y\ \mathrm{cond}\ Z \quad\text{iff}\quad & 0 \in C \text{ and } X \subseteq Z \text{ or} \\
& 1 \in C \text{ and } Y \subseteq Z \text{ or} \\
& 0, 1 \in C \text{ and } \Delta \subseteq Z ,
\end{aligned}
$$
where $C \in T$ and $X \in D$ and $Y \in D$ and where we are using the construction of Exercise 3.14.) Find a similar operator in the domain

$$
T \times D_0 \times D_1 \to D_0 + D_1 .
$$

Show also there is an approximable mapping

$$
\mathrm{which} : D_0 + D_1 \to T
$$

such that for all $x \in |D_0 + D_1|$

$$
\mathrm{cond}(\mathrm{which}(x), \mathrm{in}_0(\mathrm{out}_0(x)), \mathrm{in}_1(\mathrm{out}_1(x))) = x .
$$

**Lean 4**

- [NeighbourhoodSystems/DomainConstructs/Exercise326.lean](../Exercise326.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/Basic.lean](../Exercise326/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/TD.lean](../Exercise326/TD.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/Tmem_eq_one.lean](../Exercise326/Tmem_eq_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/Tmem_eq_zero.lean](../Exercise326/Tmem_eq_zero.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond.lean](../Exercise326/cond.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard.lean](../Exercise326/condGuard.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_master.lean](../Exercise326/condGuard_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_one.lean](../Exercise326/condGuard_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/condGuard_zero.lean](../Exercise326/condGuard_zero.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_bot.lean](../Exercise326/cond_bot.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_components.lean](../Exercise326/cond_components.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_false.lean](../Exercise326/cond_false.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_toElementMap_mem.lean](../Exercise326/cond_toElementMap_mem.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/cond_true.lean](../Exercise326/cond_true.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/one_ne_master.lean](../Exercise326/one_ne_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/zero_ne_master.lean](../Exercise326/zero_ne_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326/zero_ne_one.lean](../Exercise326/zero_ne_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum.lean](../Exercise326Sum.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_master.lean](Tmem_ge_master.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_one.lean](Tmem_ge_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/Tmem_ge_zero.lean](Tmem_ge_zero.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum.lean](condSum.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSumEmb.lean](condSumEmb.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSumEmb_toElementMap.lean](condSumEmb_toElementMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_bot.lean](condSum_bot.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_false.lean](condSum_false.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/condSum_true.lean](condSum_true.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/cond_which.lean](cond_which.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inMapu2080_outMapu2080_eq_of_left.lean](inMapu2080_outMapu2080_eq_of_left.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inMapu2081_outMapu2081_eq_of_right.lean](inMapu2081_outMapu2081_eq_of_right.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inter_in_oneset.lean](inter_in_oneset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/inter_in_zeroset.lean](inter_in_zeroset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/not_sum_mem_empty.lean](not_sum_mem_empty.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/sum_element_trichotomy.lean](sum_element_trichotomy.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard.lean](whichGuard.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_left.lean](whichGuard_left.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_masterC.lean](whichGuard_masterC.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichGuard_right.lean](whichGuard_right.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/whichMap.lean](whichMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/which_mem_one.lean](which_mem_one.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise326Sum/which_mem_zero.lean](which_mem_zero.lean)
