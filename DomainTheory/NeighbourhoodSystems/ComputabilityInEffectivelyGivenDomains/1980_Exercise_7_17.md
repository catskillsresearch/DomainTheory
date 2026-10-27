# Exercise 7.17

**EXERCISE 7.17.** Complete the proof of 7.7 for showing that $D^{\S}$ is effectively given if $D$ is. Include all the combinators of 6.2. Prove also that if $E$ is effectively given and $u : D \to E$ and $v : E \times E \to E$ are computable, then the unique strict mapping $g : D^{\S} \to E$, where, for $x \in |D|$ and $y, z \in |E|$,

$$g(\mathrm{in}(x)) = u(x), \quad \text{and}$$

$$g(\mathrm{pair}(y, z)) = v(g(y), g(z)),$$

is a computable mapping.

**[Exercise_7_17.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_17.lean)**

@import "Exercise_7_17.lean"
