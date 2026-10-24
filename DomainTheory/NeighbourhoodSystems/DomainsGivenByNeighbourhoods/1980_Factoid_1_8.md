# Factoid 1.8

## Factoid 1.8a1 — bottom element

DEFINITION 1.8. For $x, y \in |\mathcal{D}|$, we say that $x$ *approximates* $y$ iff $x \subseteq y$. The element that approximates all others, $\{\Delta\}$, is called $\perp$ (read: *bottom*); it is the "least defined" element, or the "most partial" element. Elements maximal with respect to the approximation relation are called *total elements*. $\square$

## Factoid 1.8a2 — bottom is least

DEFINITION 1.8. For $x, y \in |\mathcal{D}|$, we say that $x$ *approximates* $y$ iff $x \subseteq y$. The element that approximates all others, $\{\Delta\}$, is called $\perp$ (read: *bottom*); it is the "least defined" element, or the "most partial" element. Elements maximal with respect to the approximation relation are called *total elements*. $\square$

## Factoid 1.8b — finite filters are principal

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

## Factoid 1.8c — prefix order

Again there is an exercise here to show $\sigma x \in |B|$. In particular $\sigma\perp \in |B|$ for all $\sigma \in \Sigma^*$, and these are just the finite elements. The minimal element of $\sigma\perp$ is $\sigma\Delta$. Note that $\sigma_0\perp \subseteq \sigma_1\perp$ if and only if $\sigma_0$ is an *initial segment* of the sequence $\sigma_1$.

If now $x \in |B|$ is any explicitly given element (that is, if we know for any $X \in B$ whether or not $X \in x$), we have but to work out from these definitions that

$$

## Factoid 1.8d — union of finite approximations

x = \bigcup_{n=0}^{\infty} \sigma_n\perp,
$$

where the $\sigma_n \in \Sigma^*$ and each $\sigma_n$ is an initial segment of the next $\sigma_{n+1}$. *In general, in any domain, an element is uniquely determined by its finite approximations, and we are just making this explicit in $|B|$.* When we have complete knowledge of $x$, then there are two cases: either the approximations $\sigma_n\perp$ become constant from some point on (where $n > n_0$), or not. In the first case $x$ is finite and equal to $\sigma_{n_0}\perp$; in the second case $x$ is infinite and the $\sigma_n$ fill out an infinite (one-way) sequence.

The generalization of 1.5 to the infinite case where $\Delta = \mathbf{N} = \{0, 1, 2, 3, \ldots, n, \ldots\}$ can be made in more than one way: for instance either we use as neighbourhoods *all* non-empty subsets of $\Delta$ or just those omitting but a finite number of integers. And, as will become apparent, there are other choices giving domains of quite different characters. $\square$

Many constructions (choices of $\mathcal{D}$) lead to the "same" domain; "sameness" is an important notion and it is to be defined in terms of "isomorphism", which in turn is to be defined in terms of approximation preserving correspondences.

## AI: Human-English to AI-Lean

**[Factoid_1_8.lean](Factoid_1_8.lean)**

@import "Factoid_1_8.lean"
