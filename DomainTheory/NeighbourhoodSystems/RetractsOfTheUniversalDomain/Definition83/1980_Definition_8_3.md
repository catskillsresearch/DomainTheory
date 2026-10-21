# Definition 8.3

Not every retraction comes from a relationship like $D \triangleleft E$; in fact, we can see from the definition of $a$ above that $a \sqsubseteq 1_E$. But, as is indicated in Exercise 8.11, even this condition is not sufficient to characterize the kind of retractions provided by 8.2. The characterization is as follows.

**DEFINITION 8.3.** A retraction $a : E \to E$ is called a *projection* provided

$$a \sqsubseteq 1_E;$$

it is *finitary* iff its fixed-point set is isomorphic to a domain. $\square$

**EXAMPLES 8.4.** If a system $D$ over $\Delta$ is not trivial, then the two element system $O = \{\{0\}, \{0,1\}\}$ comes from a retraction on $D$. Specifically, define a combinator

$$\mathrm{check} : D \to O$$

by the relation

$$X \ \mathrm{check}\ Y \quad \text{iff either } Y = \{0,1\} \text{ or } X \neq \Delta.$$

We see $\mathrm{check}(x) = \bot_O$ iff $x = \bot_D$. We leave to the reader the definition of a combinator:

$$\mathrm{fade} : O \times D \to D,$$

where we have for $t \in |O|$ and $x \in |D|$:

$$\begin{aligned}
\mathrm{fade}(t,x) &= \bot_D, \text{ if } t = \bot_O; \\
&= x, \text{ if not.}
\end{aligned}$$

Now, take any $u \in |D|$ with $u \neq \bot$, and define

$$a(x) = \mathrm{fade}(\mathrm{check}(x), u).$$

Then $a$ is a retraction (not a projection in general) and the range of $a$ is isomorphic to $O$.
Another way of using these combinators is to find $(D \to_{\perp} E)$ as a retraction of $(D \to E)$. Specifically, define a combinator

$$\mathrm{strict} : (D \to E) \to (D \to E)$$

by the equation

$$\mathrm{strict}(f) = \lambda x.\ \mathrm{fade}(\mathrm{check}(x), f(x)),$$

where this time

$$\mathrm{fade} : O \times E \to E\ .$$

The range of $\mathrm{strict}$ consists exactly of the strict functions and this time $\mathrm{strict}$ is a projection whose range is indeed a domain.

Similarly, we can find a projection on $D \times E$ with a range isomorphic to $D \otimes E$ by the combinator such that:

$$\mathrm{smash}(x, y) = \mathrm{fade}(\mathrm{check}(x), \mathrm{fade}(\mathrm{check}(y), \langle x, y \rangle)),$$

for $x \in |D|$ and $y \in |E|$. $\square$

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83.lean](../Definition83.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83/IsFinitary.lean](IsFinitary.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83/IsFinitaryProjection.lean](IsFinitaryProjection.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83/IsProjection.lean](IsProjection.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83/isFinitaryProjection_retractionOfSubsystem.lean](isFinitaryProjection_retractionOfSubsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83/isFinitary_retractionOfSubsystem.lean](isFinitary_retractionOfSubsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83/isProjection_retractionOfSubsystem.lean](isProjection_retractionOfSubsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition83/retractionOfSubsystem_le_idMap.lean](retractionOfSubsystem_le_idMap.lean)
