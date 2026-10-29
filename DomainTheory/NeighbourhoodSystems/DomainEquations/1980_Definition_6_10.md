# Definition 6.10

**DEFINITION 6.10.** For two neighbourhood systems $D$ and $E$ we write

$$
D \triangleleft E
$$

to mean that these are neighbourhood systems over the same set of tokens $\Delta$ and not only is $D \subseteq E$ but whenever $X, Y \in D$ and $X \cap Y \in E$, then $X \cap Y \in D$. $\square$

For the subdomain relation $D \triangleleft E$ to hold, $D$ has to be a smaller family of neighbourhoods, but the notion of consistency in $D$ also has to be the same as in $E$. Note that if $D_0 \triangleleft E$ and $D_1 \triangleleft E$ then

<!-- page 106 -->

$$
D_0 \triangleleft D_1 \text{ iff } D_0 \subseteq D_1.
$$

It is also easy to prove that the union of a directed family of subdomains of $E$ is again a subdomain. As a consequence of this remark we have:

**[Definition_6_10.lean](Definition_6_10.lean)**

@import "Definition_6_10.lean"
**[NeighbourhoodSystems/DomainEquations/Example_6_1.lean](Example_6_1.lean)**

@import "Example_6_1.lean"
**[NeighbourhoodSystems/DomainEquations/Example_6_2.lean](Example_6_2.lean)**

@import "Example_6_2.lean"
