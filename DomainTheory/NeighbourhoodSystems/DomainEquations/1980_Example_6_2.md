# Example 6.2

**EXAMPLE 6.2.** Our staple examples $B$ and $C$ satisfy “domain equations” in the form of isomorphisms as we have previously seen. Indeed

$$
B \cong B + B, \text{ and}
$$

$$
C \cong \{\{\Lambda\}\} + C + C,
$$

where if we liked we could construct both systems over $\{0,1\}^*$ and have:

$$
B = \{\{0,1\}^*\} \cup \{0X \mid X \in B\} \cup \{1X \mid X \in B\}, \text{ and}
$$

$$
C = \{\{0,1\}^*\} \cup \{\{\Lambda\}\} \cup \{0X \mid X \in C\} \cup \{1X \mid X \in C\}.
$$

We leave to the exercises the explanations of what kinds of algebras $B$ and $C$ are and why they are initial. Here we want to propose a simple, yet interesting generalization of $B$.

Consider this domain equation:

$$
A \cong A^n + A^n,
$$

where $A^n$ stands for the $n$-fold cartesian power of $A$. We can, with the aid of some encoding solve this equation as a neighbourhood system over $\{0,1\}^*$ as follows:

$$
A = \{\{0,1\}^*\} \cup \bigcup_{i=0,1} \left\{ i \bigcup_{j < n} 1^j 0 X_j \mid X_j \in A \text{ for all } j < n \right\}.
$$

For instance, if $n = 3$, then a typical neighbourhood in $A$ is something like

$$
00X_0 \cup 010X_1 \cup 0110X_2,
$$

where $X_0, X_1, X_2 \in A$. The first ‘0’ could also be a ‘1’ in front of each of the terms.

In words, an element of $A$ (other than $\bot$) is an $n$-tuple of elements of $A$: but there are two separate copies of these, the left one and the right one. We can write for $a \in |A|$

$$
a = \pm \langle a_0, a_1, \ldots, a_{n-1} \rangle,
$$

where $+$ is chosen if $a$ is on the right, and $-$ if on the left. As a tree diagram $a$ might look like this for $n = 3$:

<!-- page 100 -->

```
                         a  +
                        / | \
                       + a₁− +
                      /|\ /|\ /|\
                     + − − + + a₁₂− − + −
                    etc. etc. etc.
```

That is, $a$ is an infinite ternary tree with $+$ or $-$ labels at each node. If each node (subtree) is truly infinite, the element is *total*; if $\perp$ is ever encountered, it is only *partial*; if every branch ends with $\perp$, the tree is a *finite element* of $|A|$.

What can be done with such trees? Let $\sigma \in \{0, 1, \ldots, n-1\}^*$ be a finite sequence of "digits" each less than $n$. We let $\Sigma = \{0, 1, \ldots, n-1\}$. We can define for $a \in |A|$ the operation $\sigma \mapsto a\sigma$ by recursion on $\sigma$:

$$
a \Lambda = a, \text{ and}
$$

$$
a i \sigma = (a_i) \sigma.
$$

The $a\sigma$ are just the *subtrees* of $a$ with $\sigma$ as a *selector*. We also have a map

$$
\mathrm{pos} : A \to T
$$

where

$$
\mathrm{pos}(+\langle a_0, a_1, \ldots, a_{n-1} \rangle) = \mathrm{true}, \text{ and}
$$

$$
\mathrm{pos}(-\langle a_0, a_1, \ldots, a_{n-1} \rangle) = \mathrm{false}.
$$

We say that a (total) tree $a$ is *eventually periodic* iff the set $\{a\sigma \mid \sigma \in \Sigma^*\}$ is finite. The result is that the "language"

$$
L_a = \{\sigma \in \Sigma^* \mid \mathrm{pos}(a\sigma) = \mathrm{true}\}
$$

corresponding to an eventually periodic tree is always a *regular event* of automata theory, and every such language has this form. In fact, $a$ just represents the initial state of an automaton, and $a\sigma$ represents the state after "reading" a tape $\sigma$. $\square$

<!-- page 101 -->

In order to formulate more generally the idea of a domain equation and initial algebra, we must introduce a small amount of the terminology of category theory. To be as specific as possible, think of systems $D$ over sets $\Delta \subseteq \Sigma^*$ with $\Sigma = \{0, 1\}$, say. They form quite an interesting category with respect to the approximable maps $f : D \to D'$. Recall that to be a category of "domains" and "maps" all that is required is an associative composition $g \circ f$ of maps with identity maps $I : D \to D$ for each domain of the category. And this we certainly have for the systems indicated. And there are many other categories waiting around: for instance, restrict systems to those where $\emptyset \notin D$. This is not much of a restriction, as every system is isomorphic to one like this. Or restrict the maps to being the strict maps $f : D \to D'$ where $f(\bot_D) = \bot_{D'}$. This is an essentially different, though related category. We shall find many others.

What examples 6.1 and 6.2 suggest is the notion of a construct which makes new domains out of old. For example, with $D$ fixed, 6.1 suggests for any domain $X$ over $\Gamma \subseteq \Sigma^*$ a domain

$$
T(X) = D + (X \times X).
$$

More specifically (converting from $\Sigma = \{0, 1, 2\}$ to $\Sigma = \{0, 1\}$) we could write

$$
T(X) = \{\Gamma'\} \cup \{0X \mid X \in D\} \cup \{10X \cup 11Y \mid X, Y \in X\},
$$

where we have $\Gamma' = 0\Delta \cup 10\Gamma \cup 11\Gamma$. (By the way, here we definitely want to assume $\emptyset \notin D$ and $\emptyset \notin X$ and to get $\emptyset \notin T(X)$.) This construct is an example of a *functor*, a notion that can be defined abstractly on any category.

**[Example_6_2.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Example_6_2.lean)**

@import "Example_6_2.lean"
