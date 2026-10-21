# Exercise 3.28

**EXERCISE 3.28.** In the function space $(D_0 \to D_1)$ let

$$
\bigcap \{ [X_i, Y_i] \mid i < n \}
$$

be a (non-empty) neighbourhood. In 3.9 the minimal element of this neighbourhood is characterized as a relation $f_0$. Show that as an elementwise mapping it can be defined by the formula

$$
f_0(x) = \bigsqcup \{ \uparrow Y_i \mid x \in [X_i] \} ,
$$

for $x \in |D_0|$. Try to draw a picture of $|D_0|$ with neighbourhoods $[X_i]$ and the corresponding values of the function $f_0$.

**Lean 4**

- [NeighbourhoodSystems/DomainConstructs/Exercise328.lean](../Exercise328.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/Elementu2emem_interYs_of.lean](Elementu2emem_interYs_of.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/leastMapVals.lean](leastMapVals.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/leastMapVals_bounded.lean](leastMapVals_bounded.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/leastMap_toElementMap_le_of_ub.lean](leastMap_toElementMap_le_of_ub.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/toElementMap_leastMap_eq_sSup.lean](toElementMap_leastMap_eq_sSup.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise328/val_le_leastMap_toElementMap.lean](val_le_leastMap_toElementMap.lean)
