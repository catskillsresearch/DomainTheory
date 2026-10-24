# Examples 8.4

## Human-English

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

<!-- page 137 -->

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

## AI: Human-English to AI-Lean

**[Examples_8_4.lean](Examples_8_4.lean)**

@import "Examples_8_4.lean"
