# Exercise 3.22

**EXERCISE 3.22.** Prove that there is an approximable mapping

$$
\text{comp} : (D_1 \to D_2) \times (D_0 \to D_1) \to (D_0 \to D_2)
$$

where for all $g : D_1 \to D_2$ and $f : D_0 \to D_1$ we have

$$
\text{comp}(g, f) = g \circ f.
$$

Show this directly by writing down the neighbourhood relation and by building the mapping up from eval and curry (on suitable domains) using $\circ$ and $\langle,\,\rangle$. (Hint: Fill in maps in the following sequence of domains:

1. $(D_0 \to D_1) \times D_0 \to D_1$
2. $(D_1 \to D_2) \times ((D_0 \to D_1) \times D_0) \to (D_1 \to D_2) \times D_1$
3. $((D_1 \to D_2) \times (D_0 \to D_1)) \times D_0 \to (D_1 \to D_2) \times D_1$
4. $((D_1 \to D_2) \times (D_0 \to D_1)) \times D_0 \to D_2$
5. $(D_1 \to D_2) \times (D_0 \to D_1) \to (D_0 \to D_2)$.

The maps are of course not uniquely determined, but the shifting of brackets ought to suggest the right choice.)

**Lean 4**

- [NeighbourhoodSystems/DomainConstructs/Exercise322/compApp.lean](compApp.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/compMap.lean](compMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/toElementMap_compApp.lean](toElementMap_compApp.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/toElementMap_compMap_apply.lean](toElementMap_compMap_apply.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322/toApproxMap_compMap.lean](toApproxMap_compMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise322.lean](../Exercise322.lean)
