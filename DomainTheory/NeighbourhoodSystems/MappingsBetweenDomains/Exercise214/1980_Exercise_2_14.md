# Exercise 2.14

**EXERCISE 2.14.** Let $f : |D_0| \to |D_1|$ be an isomorphism between domains. Let $\varphi : D_0 \to D_1$ be the one-one correspondence between neighbourhoods provided by Theorem 2.7 where

$$
f(\uparrow X) = \uparrow \varphi(X)
$$

for all $X \in D_0$. Show that the approximable mapping determined by $f$ is just the relationship $\varphi(X) \subseteq Y$. In addition prove that if $X, X' \in D_0$ are consistent, then

$$
\varphi(X \cap X') = \varphi(X) \cap \varphi(X').
$$
Remark that the isomorphisms between domains correspond exactly to the isomorphisms between neighbourhood systems (in the sense of one-one inclusion preserving correspondences).

**Lean 4**

- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise214.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise214.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/Basic.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/Basic.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/phi.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/phi.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/phi_inter.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/phi_inter.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/phi_mem.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/phi_mem.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/phi_spec.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/phi_spec.lean)
- [NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/rel_ofIso_iff.lean](DomainTheory/NeighbourhoodSystems/MappingsBetweenDomains/Exercise214/rel_ofIso_iff.lean)
