# Exercise 7.20

**EXERCISE 7.20.** Show that there is a combinator

$$\text{union} : \mathbb{P}(\mathbb{P} D) \to \mathbb{P} D$$

where for suitable neighbourhoods

$$\bigcup_{i < n} \downarrow \Bigl(\bigcup_{j < m_i} \downarrow X_{ij}\Bigr) \quad \text{union} \quad \bigcup_{k < q} \downarrow Y_k \quad \text{iff} \quad \forall i < n \forall j < m_i \exists k < q.\, X_{ij} \subseteq Y_k \, .$$

Is union computable if $D$ is effectively given? What is

$$\text{union}(\{\{x\}, \{y, z\}\}) = ??$$

Are $\mathbb{P}(\mathbb{P} D)$ and $\mathbb{P} D$ generally isomorphic??

**[Exercise_7_20.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_20.lean)**

@import "Exercise_7_20.lean"
