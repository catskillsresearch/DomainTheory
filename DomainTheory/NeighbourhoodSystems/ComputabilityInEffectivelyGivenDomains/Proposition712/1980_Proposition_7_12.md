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

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/HasTop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/HasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDext.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDext.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_PD.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_PD.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMapu2082_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMap₂.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoinApproxMap₂.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_inter_two.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_inter_two.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_pair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDfinJoin_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel_Ypd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_rel_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonApproxMap_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet_mem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingletonMeet_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_mono.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_principal.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/PDsingleton_principal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_false.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_false.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_true.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_mem_true.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_hasTop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_hasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_mem_empty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/Vshape_not_mem_empty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ext_of_principal.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ext_of_principal.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_toElementMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/finJoinMap_prod_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ft_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/ft_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_inter_closed.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_inter_closed.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_iso.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_iso.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_trianglelefteq_powerDomain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/hasTop_of_trianglelefteq_powerDomain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/improperTop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/improperTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/powerDomain_hasTop.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/powerDomain_hasTop.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/singleton_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/singleton_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/subsystem_inter_closed.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/subsystem_inter_closed.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/tf_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/tf_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/vshape_not_trianglelefteq_powerDomain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition712/vshape_not_trianglelefteq_powerDomain.lean)
