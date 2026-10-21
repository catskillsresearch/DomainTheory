# Exercise 5.14

**EXERCISE 5.14.** Show that there are approximable mappings

$$
\mathrm{graph} : (P\mathbf{N} \to P\mathbf{N}) \to P\mathbf{N} \quad \text{and} \quad \mathrm{fun} : P\mathbf{N} \to (P\mathbf{N} \to P\mathbf{N}),
$$

where we have

$$
\mathrm{fun} \circ \mathrm{graph} = \lambda f.\, f, \quad \text{and} \quad \mathrm{graph} \circ \mathrm{fun} \supseteq \lambda x.\, x.
$$

(Hint: Using the notation

$$
[n_0, n_1, \ldots, n_k] = \mathrm{num}(n_0, [n_1, \ldots, n_k])
$$

two such combinators can be given by formulae

$$
\mathrm{fun}(u)(x) = \{m \mid \exists n_0, \ldots, n_{k-1} \in x.\ [n_0+1, \ldots, n_{k-1}+1, 0, m] \in u\}
$$

$$
\mathrm{graph}(f) = \{[n_0+1, \ldots, n_{k-1}+1, 0, m] \mid m \in f(\{n_0, \ldots, n_{k-1}\})\}
$$

where $k$ is variable — meaning all finite sequences are to be considered.)

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Basic.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Basic.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_Graph.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_Graph.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_isApprox.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_isApprox.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_mono.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Fun_mono.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Graph.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/Graph.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/IsApprox.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/IsApprox.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/entries.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/entries.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/id_le_Graph_Fun.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/id_le_Graph_Fun.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/mem_entries.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/mem_entries.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/num_succ_left_gt.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/num_succ_left_gt.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_cons.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_cons.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_injective.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_injective.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_nil.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_nil.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_surjective.lean](DomainTheory/NeighbourhoodSystems/TypedLambdaCalculus/Exercise514/tag_surjective.lean)
