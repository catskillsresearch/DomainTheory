# Proposition 2.11

It would seem that the continuous lattices are starting to sound suspiciously like the injective spaces. Indeed, if we can prove the following, the circle will be complete.

**2.11 Proposition.** Every continuous lattice is an injective space under its induced topology.

++Proof of 2.11++: Let $D$ be a continuous lattice with its induced topology, and let $X \subseteq Y$ be two $T_0$-spaces in the subspace relation. Suppose

$$f : X \to D$$

is continuous. Define

$$\bar{f} : Y \to D$$

by the formula:

$$\bar{f}(y) = \bigsqcup \sqcap f(x) : x \in X \cap U : y \in U ,$$

where $U$ ranges over the open subsets of $Y$. We need to show that $\bar{f}$ extends $f$ and that it is continuous.

First, the continuity: Suppose that $d \in D$ and $d \ll \bar{f}(y)$; that is, $\bar{f}(y)$ belongs to a typical basic open subset of $D$. Since $D$ is continuous, we can also find

$$d \ll d' \ll \bar{f}(y)$$

with $d' \in D$. From the definition of $\bar{f}$ it follows that

$$d' \sqsubseteq \sqcap f(x) : x \in X \cap U $$

for some open $U \subseteq Y$ with $y \in U$. Thus

$$d' \sqsubseteq \bar{f}(y')$$

for all $y' \in U$ by virtue of the definition of $\bar{f}$. Since $d \ll d'$, we have also

$$d \ll \bar{f}(y')$$

for all $y' \in U$; in other words, the inverse image of the open subset of $D$ determined by $d$ under $\bar{f}$ is indeed open in $Y$, and $\bar{f}$ is thus continuous.

Next, the extension property: Note that the relationship

$$\bar{f}(x') \sqsubseteq f(x')$$

for all $x' \in X$ comes directly out of the definition of $\bar{f}$. For the converse, suppose $d \ll f(x')$ where $d \in D$. By assumption $f : X \to D$ is continuous, so

$$d \ll f(x'')$$

for all $x'' \in X \cap U$ where $U$ is a suitable open subset of $Y$ with $x' \in U$. In particular we have:

$$d \sqsubseteq \sqcap f(x'') : x'' \in X \cap U ,$$

and so $d \sqsubseteq \bar{f}(x')$. Since $d \ll f(x')$ always implies $d \sqsubseteq \bar{f}(x')$, we see that $f(x') \sqsubseteq \bar{f}(x')$ follows by the continuity of $D$, and the proof is complete. $\square$

**Lean 4**

- [ContinuousLattice/Constructions/proposition_2_11.lean](DomainTheory/ContinuousLattice/Constructions/proposition_2_11.lean)
