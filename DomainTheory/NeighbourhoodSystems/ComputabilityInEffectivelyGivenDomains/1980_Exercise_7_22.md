# Exercise 7.22

**EXERCISE 7.22.** (For algebraists.) Let $\Sigma = \{0,1\}^*$ be the free semigroup. A new domain is constructed by defining a family of sets by the least fixed point theorem as follows:

$$S = \{\Sigma\} \cup \{\{\sigma\} \mid \sigma \in \Sigma\} \cup \{XY \mid X, Y \in S\} \cup \{X \cap Y \mid X, Y \in S \text{ and } X \cap Y \neq \emptyset\}.$$

Here we write: $XY = \{\sigma\tau \mid \sigma \in X \text{ and } \tau \in Y\}$.

Prove that $S$ is an effectively given, positive neighbourhood system. (Hint: The sets in $S$ are each “regular events” in the terminology of automata theory, and we have a decision method for the set algebra of regular events.)

Define multiplication on $|S|$ by

$$xy = \{Z \in S \mid \exists X \in x \ \exists Y \in y.\ XY \subseteq Z\},$$

and show $|S|$ becomes a semigroup with $\Sigma$ embedded into $|S|$ by the homomorphism $\sigma \mapsto \{X \in S \mid \sigma \in X\}$.

Investigate some *infinite words* in $S$, say those defined by least fixed points such as: $\vec{\sigma} = \sigma\,\vec{\sigma}$ and $\vec{\sigma} = \vec{\sigma}\,\sigma$. Are these equations true:

$$\vec{\sigma}\,\vec{\sigma} = \vec{\sigma}, \quad \vec{\sigma}\,\vec{\sigma}\,\vec{\sigma} = \vec{\sigma}, \quad \vec{\sigma}\,\vec{1}\,\vec{\sigma}\,\vec{1} = \vec{\sigma}\,\vec{1},$$

and $\vec{01}\,\vec{01}\,\vec{01}\,\vec{01} = \vec{01}\,\vec{01}$ ?

**[Exercise_7_22.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_22.lean)**

@import "Exercise_7_22.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition_7_1.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition_7_1.lean)**

@import "Definition_7_1.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition_7_2.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition_7_2.lean)**

@import "Definition_7_2.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition_7_3.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition_7_3.lean)**

@import "Proposition_7_3.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example_7_8.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Example_7_8.lean)**

@import "Example_7_8.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_13.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_13.lean)**

@import "Exercise_7_13.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_14.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_14.lean)**

@import "Exercise_7_14.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition_7_10.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition_7_10.lean)**

@import "Proposition_7_10.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition_7_11.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition_7_11.lean)**

@import "Definition_7_11.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_19.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_19.lean)**

@import "Exercise_7_19.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_20.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_20.lean)**

@import "Exercise_7_20.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_21.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_21.lean)**

@import "Exercise_7_21.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition_7_7.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition_7_7.lean)**

@import "Proposition_7_7.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem_7_4.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem_7_4.lean)**

@import "Theorem_7_4.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition_7_12.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Proposition_7_12.lean)**

@import "Proposition_7_12.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem_7_5.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem_7_5.lean)**

@import "Theorem_7_5.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_15.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_15.lean)**

@import "Exercise_7_15.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_16.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_16.lean)**

@import "Exercise_7_16.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_18.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_18.lean)**

@import "Exercise_7_18.lean"
**[NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_17.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise_7_17.lean)**

@import "Exercise_7_17.lean"
