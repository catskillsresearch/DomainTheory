# Examples 1.2–1.5 (Revisited)

EXAMPLES 1.2 – 1.5 (Revisited). The examples as given were all finite, so any explicitly given filter $x$ is principal, the element is finite, the minimal $X \in x$ tells us all we need to know. In such simple situations there is essentially no difference between elements and neighbourhoods — except for the reversal of the order as noted. This (necessary) reversal should not, however, become a matter of confusion: the smaller the neighbourhood has become, the more it has "converged", and so the better defined the element has become. In the approximation relation the "poorer" elements are placed below the "better" with the total up at the top. This will become clearer in discussing "infinite" elements.

Example 1.3 will be generalized in Exercise 1.12. Let us here generalize first 1.4. We let

$$
\Delta = \Sigma^*,
$$

where $\Sigma = \{0, 1\}$ and $\Sigma^*$ means the set of all finite sequences of 0's and 1's, with $\Lambda$ being the empty sequence. We write $\sigma\tau$ for the *concatenation* or *juxtaposition* of two sequences $\sigma, \tau \in \Sigma^*$. Define

$$
B = \{\sigma\Sigma^* \mid \sigma \in \Sigma^*\}, \text{ where}
$$

$$
\sigma X = \{\sigma\tau \mid \tau \in X\},
$$

for an arbitrary set $X \subseteq \Sigma^*$. In other words, a neighbourhood in $B$ consists of all *extensions* of a given sequence $\sigma$. (Refer back to the finite version of 1.4.) We use the letter "B" to remind us of "binary", and this is an example we shall refer to many times. The proof (if it is not obvious) that $B$ is a neighbourhood system should be done as an exercise.

What do we find in $|B|$? Of course $\perp = \{\Delta\} \in |B|$. For any $x \in |B|$ and $\sigma \in \Sigma^*$ define

$$
\sigma x = \{Y \mid \sigma X \subseteq Y \text{ some } X \in x\}.
$$

<!-- page 15 -->

**[Examples_1_2_1_5_revisited.lean](Examples_1_2_1_5_revisited.lean)**

@import "Examples_1_2_1_5_revisited.lean"
