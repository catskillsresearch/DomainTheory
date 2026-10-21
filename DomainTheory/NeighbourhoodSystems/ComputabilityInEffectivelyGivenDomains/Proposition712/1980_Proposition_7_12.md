# Proposition 7.12

**PROPOSITION 7.12.** The mapping

$$\lambda x_0, \dots, x_{n-1}.\, \{x_0, \dots, x_{n-1}\} : D^n \to \mathbb{P} D$$

is approximable and is computable if $D$ is effectively given. Moreover, the map $\lambda x.\, \{x\}$ shows that $D \trianglelefteq \mathbb{P} D$, and we also have the law:

$$\{x_0, \dots, x_{n-1}\} = \{x_0\} \cap \dots \cap \{x_{n-1}\}$$

as an intersection of filters.

*Proof* : The second part shows that everything reduces to $\lambda x.\, \{x\}$. We see that

$$X_k\ (\lambda x.\, \{x\})\ \bigcup_{i<q} (\uparrow X_{n_i}) \text{ iff } \exists i < q.\, X_k \sqsubseteq X_{n_i}.$$

Thus, $\lambda x.\, \{x\}$ is an approximable mapping and is computable in the effectively given case.

The proof of the law can be reduced to the special case

$$\{x\} \cap \{y\} = \{x, y\}$$

for the sake of illustration. In terms of finite elements of the two domains $D$ and $\mathbb{P} D$ we find

$$\{\uparrow X\} = \uparrow\uparrow X,$$

and so,

$$\begin{aligned}
\{\uparrow X\} \cap \{\uparrow Y\} &= \uparrow\uparrow X \cap \uparrow\uparrow Y \\
&= \uparrow(\uparrow X \cup \uparrow Y) \\
&= \{\uparrow X, \uparrow Y\}.
\end{aligned}$$

An equation between approximable functions that checks for finite elements also holds for all elements.

Finally, we note that

$$D \cong D^\dagger \trianglelefteq \mathbb{P} D$$
and that the isomorphism involved is just $\lambda x.\,\{x\}$ by what we saw on the finite elements. $\square$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712.lean](../Proposition712.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/HasTop.lean](HasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDext.lean](PDext.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_isComputable.lean](PDfinJoinApproxMapu2082_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_PD.lean](PDfinJoinApproxMapu2082_rel_PD.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_iff.lean](PDfinJoinApproxMapu2082_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_toElementMap.lean](PDfinJoinApproxMapu2082_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMap₂.lean](PDfinJoinApproxMap₂.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_inter_two.lean](PDfinJoin_inter_two.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_pair.lean](PDfinJoin_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap.lean](PDsingletonApproxMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel.lean](PDsingletonApproxMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel_Ypd_iff.lean](PDsingletonApproxMap_rel_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_toElementMap.lean](PDsingletonApproxMap_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet.lean](PDsingletonMeet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet_mem.lean](PDsingletonMeet_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_mono.lean](PDsingleton_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_principal.lean](PDsingleton_principal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape.lean](Vshape.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_false.lean](Vshape_mem_false.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_true.lean](Vshape_mem_true.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_hasTop.lean](Vshape_not_hasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_mem_empty.lean](Vshape_not_mem_empty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ext_of_principal.lean](ext_of_principal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod.lean](finJoinMap_prod.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_rel.lean](finJoinMap_prod_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_toElementMap.lean](finJoinMap_prod_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ft_inter.lean](ft_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_inter_closed.lean](hasTop_of_inter_closed.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_iso.lean](hasTop_of_iso.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_trianglelefteq_powerDomain.lean](hasTop_of_trianglelefteq_powerDomain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/improperTop.lean](improperTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/powerDomain_hasTop.lean](powerDomain_hasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/singleton_isComputable.lean](singleton_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/subsystem_inter_closed.lean](subsystem_inter_closed.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/tf_inter.lean](tf_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/vshape_not_trianglelefteq_powerDomain.lean](vshape_not_trianglelefteq_powerDomain.lean)
