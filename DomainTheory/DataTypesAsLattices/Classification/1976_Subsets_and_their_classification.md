# Subsets and their classification

Retracts produce very special subsets of $\mathbf{P}\omega$: a retract always has a nonempty range which forms a lattice under $\sqsubseteq$. For example, the range of **int** is $\{\bot, \top\} \cup \omega$. We often wish to eliminate $\bot$ and $\top$; and with a retract like **tree** the situation is more complex, since combinations like $\langle 1, \langle \langle 1, \langle \bot, \langle 0 \rangle \rangle \rangle, \top \rangle \rangle$ might require elimination. In these two cases the method is simple.

Consider these two functions:

$$(6.1) \quad \mathbf{mid} = \lambda x : \mathbf{int}.\, x \supset 0, 0$$

$$(6.2) \quad \mathbf{perf} = \lambda u : \mathbf{tree}.\, \mathbf{which}(u) \supset 0,\, \Delta(\mathbf{perf}(\mathbf{fst}(\mathbf{out}(u))))(\mathbf{perf}(\mathbf{snd}(\mathbf{out}(u))))$$

where $\Delta$ is a special combinator:

$$(6.3) \quad \Delta = \lambda x \lambda y.\, (x \supset (y \supset 0, \top), \top) \cup (y \supset (x \supset 0, \top), \top).$$

We find that $\omega = \{x : \mathbf{int} \mid \mathbf{mid}(x) = 0\}$. In the case of trees, note first this behavior of $\Delta$:

| $\Delta$ | $\bot$ | $0$ | $\top$ |
| :---: | :---: | :---: | :---: |
| $\bot$ | $\bot$ | $\bot$ | $\top$ |
| $0$ | $\bot$ | $0$ | $\top$ |
| $\top$ | $\top$ | $\top$ | $\top$ |

The question is: what subset is $\{u : \mathbf{tree} \mid \mathbf{perf}(u) = 0\}$?

Now **perf** is defined recursively. We can see that

$$\mathbf{perf}(\bot) = \bot, \quad \mathbf{perf}(\top) = \top, \quad \mathbf{perf}(\langle 0 \rangle) = 0,$$

and

$$\mathbf{perf}(\langle 1, \langle x, y \rangle \rangle) = \Delta(\mathbf{perf}(x))(\mathbf{perf}(y))$$

when $x, y : \mathbf{tree}$. Every tree, aside from $\top$ or $\bot$, is either *atomic* or a pair of trees. The atomic tree is “perfect” (that is, $\mathbf{perf}(\langle 0 \rangle) = 0$). A finite tree which does not contain $\bot$ or $\top$ is perfect—as we can see inductively using the table above for $\Delta$. An infinite tree is never perfect: either some branch ends in $\top$ and **perf** maps it to $\top$, or $\top$ is never reached and **perf** maps it to $\bot$. Thus the subset in question is then seen to be the set of *finite* trees generated from the atom by pairing. This is clearly a desirable subset, and it is sorted out by a function with a simple recursive definition. The general question is: what subsets can be characterized by equations? The answer can be given by reference to the topology of $\mathbf{P}\omega$.

- [Definition (classes)](1976_Definition_classes.md)
- [Theorem 6.1](1976_Theorem_6_1.md)
- [Theorem 6.2](1976_Theorem_6_2.md)
- [Theorem 6.3](1976_Theorem_6_3.md)
- [Theorem 6.4](1976_Theorem_6_4.md)
- [Theorem 6.5](1976_Theorem_6_5.md)
- [Theorem 6.6](1976_Theorem_6_6.md)
- [Theorem 6.7](1976_Theorem_6_7.md)

**Lean 4**

- [DataTypesAsLattices/Classification.lean](DomainTheory/DataTypesAsLattices/Classification.lean)
- [DataTypesAsLattices/Classification/Basic.lean](DomainTheory/DataTypesAsLattices/Classification/Basic.lean)
- [DataTypesAsLattices/Classification/BooleanMemE.lean](DomainTheory/DataTypesAsLattices/Classification/BooleanMemE.lean)
- [DataTypesAsLattices/Classification/IsBdelta.lean](DomainTheory/DataTypesAsLattices/Classification/IsBdelta.lean)
- [DataTypesAsLattices/Classification/IsBooleanOpen.lean](DomainTheory/DataTypesAsLattices/Classification/IsBooleanOpen.lean)
- [DataTypesAsLattices/Classification/IsFcapG.lean](DomainTheory/DataTypesAsLattices/Classification/IsFcapG.lean)
- [DataTypesAsLattices/Classification/IsFcapGdelta.lean](DomainTheory/DataTypesAsLattices/Classification/IsFcapGdelta.lean)
- [DataTypesAsLattices/Classification/IsPi11.lean](DomainTheory/DataTypesAsLattices/Classification/IsPi11.lean)
- [DataTypesAsLattices/Classification/IsScottGdelta.lean](DomainTheory/DataTypesAsLattices/Classification/IsScottGdelta.lean)
- [DataTypesAsLattices/Classification/IsSigma11.lean](DomainTheory/DataTypesAsLattices/Classification/IsSigma11.lean)
- [DataTypesAsLattices/Classification/IsThreeValued.lean](DomainTheory/DataTypesAsLattices/Classification/IsThreeValued.lean)
- [DataTypesAsLattices/Classification/ScottB.lean](DomainTheory/DataTypesAsLattices/Classification/ScottB.lean)
- [DataTypesAsLattices/Classification/ScottF.lean](DomainTheory/DataTypesAsLattices/Classification/ScottF.lean)
- [DataTypesAsLattices/Classification/ScottG.lean](DomainTheory/DataTypesAsLattices/Classification/ScottG.lean)
- [DataTypesAsLattices/Classification/charOpen.lean](DomainTheory/DataTypesAsLattices/Classification/charOpen.lean)
- [DataTypesAsLattices/Classification/charTop.lean](DomainTheory/DataTypesAsLattices/Classification/charTop.lean)
- [DataTypesAsLattices/Classification/closedToZero.lean](DomainTheory/DataTypesAsLattices/Classification/closedToZero.lean)
- [DataTypesAsLattices/Classification/evenPart.lean](DomainTheory/DataTypesAsLattices/Classification/evenPart.lean)
- [DataTypesAsLattices/Classification/fcapGdeltaPack.lean](DomainTheory/DataTypesAsLattices/Classification/fcapGdeltaPack.lean)
- [DataTypesAsLattices/Classification/fcapGdeltaPack_eq.lean](DomainTheory/DataTypesAsLattices/Classification/fcapGdeltaPack_eq.lean)
- [DataTypesAsLattices/Classification/fcapGdeltaPack_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Classification/fcapGdeltaPack_isScottContinuous.lean)
- [DataTypesAsLattices/Classification/isBdelta_inter.lean](DomainTheory/DataTypesAsLattices/Classification/isBdelta_inter.lean)
- [DataTypesAsLattices/Classification/isBdelta_union.lean](DomainTheory/DataTypesAsLattices/Classification/isBdelta_union.lean)
- [DataTypesAsLattices/Classification/oddEvenPack.lean](DomainTheory/DataTypesAsLattices/Classification/oddEvenPack.lean)
- [DataTypesAsLattices/Classification/oddEvenPack_eq_zero.lean](DomainTheory/DataTypesAsLattices/Classification/oddEvenPack_eq_zero.lean)
- [DataTypesAsLattices/Classification/oddPart.lean](DomainTheory/DataTypesAsLattices/Classification/oddPart.lean)
- [DataTypesAsLattices/Classification/pairIndexed.lean](DomainTheory/DataTypesAsLattices/Classification/pairIndexed.lean)
- [DataTypesAsLattices/Classification/pairIndexed_eq_top.lean](DomainTheory/DataTypesAsLattices/Classification/pairIndexed_eq_top.lean)
- [DataTypesAsLattices/Classification/typicalBdelta.lean](DomainTheory/DataTypesAsLattices/Classification/typicalBdelta.lean)
- [DataTypesAsLattices/Classification/typicalBdelta_isBdelta.lean](DomainTheory/DataTypesAsLattices/Classification/typicalBdelta_isBdelta.lean)
- [DataTypesAsLattices/Classification/typicalF.lean](DomainTheory/DataTypesAsLattices/Classification/typicalF.lean)
- [DataTypesAsLattices/Classification/typicalF_mem_ScottF.lean](DomainTheory/DataTypesAsLattices/Classification/typicalF_mem_ScottF.lean)
- [DataTypesAsLattices/Classification/typicalF_universal.lean](DomainTheory/DataTypesAsLattices/Classification/typicalF_universal.lean)
- [DataTypesAsLattices/Classification/typicalFcapG.lean](DomainTheory/DataTypesAsLattices/Classification/typicalFcapG.lean)
- [DataTypesAsLattices/Classification/typicalFcapG_isFcapG.lean](DomainTheory/DataTypesAsLattices/Classification/typicalFcapG_isFcapG.lean)
- [DataTypesAsLattices/Classification/typicalFcapG_universal.lean](DomainTheory/DataTypesAsLattices/Classification/typicalFcapG_universal.lean)
- [DataTypesAsLattices/Classification/typicalFcapGdelta.lean](DomainTheory/DataTypesAsLattices/Classification/typicalFcapGdelta.lean)
- [DataTypesAsLattices/Classification/typicalFcapGdelta_isFcapGdelta.lean](DomainTheory/DataTypesAsLattices/Classification/typicalFcapGdelta_isFcapGdelta.lean)
- [DataTypesAsLattices/Classification/typicalFcapGdelta_universal.lean](DomainTheory/DataTypesAsLattices/Classification/typicalFcapGdelta_universal.lean)
- [DataTypesAsLattices/Classification/typicalG.lean](DomainTheory/DataTypesAsLattices/Classification/typicalG.lean)
- [DataTypesAsLattices/Classification/typicalG_isScottOpen.lean](DomainTheory/DataTypesAsLattices/Classification/typicalG_isScottOpen.lean)
- [DataTypesAsLattices/Classification/typicalG_mem_ScottG.lean](DomainTheory/DataTypesAsLattices/Classification/typicalG_mem_ScottG.lean)
- [DataTypesAsLattices/Classification/typicalG_universal.lean](DomainTheory/DataTypesAsLattices/Classification/typicalG_universal.lean)
- [DataTypesAsLattices/Classification/typicalGdelta.lean](DomainTheory/DataTypesAsLattices/Classification/typicalGdelta.lean)
- [DataTypesAsLattices/Classification/typicalGdelta_eq.lean](DomainTheory/DataTypesAsLattices/Classification/typicalGdelta_eq.lean)
- [DataTypesAsLattices/Classification/typicalGdelta_isScottGdelta.lean](DomainTheory/DataTypesAsLattices/Classification/typicalGdelta_isScottGdelta.lean)
- [DataTypesAsLattices/Classification/typicalGdelta_universal.lean](DomainTheory/DataTypesAsLattices/Classification/typicalGdelta_universal.lean)
- [DataTypesAsLattices/Classification/typicalPi11.lean](DomainTheory/DataTypesAsLattices/Classification/typicalPi11.lean)
- [DataTypesAsLattices/Classification/typicalPi11_isPi11.lean](DomainTheory/DataTypesAsLattices/Classification/typicalPi11_isPi11.lean)
- [DataTypesAsLattices/Classification/typicalPi11_universal.lean](DomainTheory/DataTypesAsLattices/Classification/typicalPi11_universal.lean)
- [DataTypesAsLattices/Classification/typicalSigma11.lean](DomainTheory/DataTypesAsLattices/Classification/typicalSigma11.lean)
- [DataTypesAsLattices/Classification/typicalSigma11_isSigma11.lean](DomainTheory/DataTypesAsLattices/Classification/typicalSigma11_isSigma11.lean)
- [DataTypesAsLattices/Classification/typicalSigma11_universal.lean](DomainTheory/DataTypesAsLattices/Classification/typicalSigma11_universal.lean)
- [DataTypesAsLattices/Classification/uvU.lean](DomainTheory/DataTypesAsLattices/Classification/uvU.lean)
- [DataTypesAsLattices/Classification/uvV.lean](DomainTheory/DataTypesAsLattices/Classification/uvV.lean)
- [DataTypesAsLattices/Classification/zeroPrime.lean](DomainTheory/DataTypesAsLattices/Classification/zeroPrime.lean)
- [DataTypesAsLattices/Classification/zero_not_mem_succSet_top.lean](DomainTheory/DataTypesAsLattices/Classification/zero_not_mem_succSet_top.lean)
