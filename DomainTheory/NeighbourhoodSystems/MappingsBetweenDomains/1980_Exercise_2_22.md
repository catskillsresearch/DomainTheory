# Exercise 2.22

## Human-English

**EXERCISE 2.22.** (For set theorists). We have remarked in Exercise 1.18 and in Exercise 2.11 that any domain $|D|$, as a family of sets (in fact, a family of subsets of the set $D$ itself), is closed under the intersection of an arbitrary non-empty sub family and under the union of any directed sub family. For those familiar with the subject matter, the example of the (proper) ideals of a commutative ring (with unit) is also seen to be such a family. What is the abstract situation? Let $\mathbf{C}$ be *any* family of sets with these closure properties. It is to be shown that $\mathbf{C}$ is inclusion-isomorphic to a domain. (Hint: Let $\Delta$ be the set of finite sets included in sets in $\mathbf{C}$. For $F \in \Delta$, define its "closure" by the equation:

$$\overline{F} = \bigcap \{ X \in \mathbf{C} \mid F \subseteq X \}.$$

Every $\overline{F} \in \mathbf{C}$, and these will prove to be the "finite" elements of $\mathbf{C}$. The neighbourhood system $\mathcal{D}$ over $\Delta$ can be taken to be the sets of the form

$$C(F) = \{ G \in \Delta \mid F \subseteq \overline{G} \}$$

for $F \in \Delta$. Notice that for all $X \in \mathbf{C}$

$$X = \bigcup \{ \overline{F} \mid F \subseteq X \text{ and } F \in \Delta \}.$$)

Check that approximable functions on these families are just those preserving directed unions.

<!-- page 37 -->

**LECTURE III**

**DOMAIN CONSTRUCTS**

Having now seen a number of domains presented through their neighbourhood systems, we need next to introduce general constructs for forming new domains from old. There are an unlimited number of such constructs (technically called *functors*), but we have time only to single out a few of the more important ones. Outstanding among all of them is the notion of product of systems, which in our chosen category has all the expected properties. For the time being in order to simplify notation we assume of the underlying sets $\Delta_0$ and $\Delta_1$ of systems $\mathcal{D}_0$ and $\mathcal{D}_1$ that they are disjoint. There is no loss of generality as $\mathcal{D}_1$ can always be replaced by an isomorphic system disjoint from $\mathcal{D}_0$ in the required sense.

## AI: Human-English to AI-Lean

**[Exercise_2_22.lean](Exercise_2_22.lean)**

@import "Exercise_2_22.lean"
