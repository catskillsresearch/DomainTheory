# Definition 3.8

**DEFINITION 3.8.** Given neighbourhood systems $D_0$ and $D_1$, the *function space* $(D_0 \to D_1)$ is the system whose set of tokens is the set of approximable mappings of Definition 2.1 and whose neighbourhoods are finite non-empty intersections of sets of the form

$$
[X, Y] = \{f : D_0 \to D_1 \mid X f Y\},
$$

where $X \in D_0$ and $Y \in D_1$. $\square$

We have been calling our mappings "approximable" for a long time now without saying exactly how they can be approximated! Definition 3.8 supplies the missing key, because once a domain has been defined, then the general theory gives an explicit meaning to the word approximation. We still have to verify, however, that the mappings do correspond to the elements of the domain.

<!-- page 43 -->

**[Definition_3_8.lean](Definition_3_8.lean)**

@import "Definition_3_8.lean"
