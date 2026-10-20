# Injective spaces

**1. INJECTIVE SPACES.** All spaces are $T_0$-spaces, and we begin by defining a class of spaces to be called *injective*.

**1.1 Definition.** A $T_0$-space $D$ is *injective* iff for arbitrary spaces $X$ and $Y$ if $X \subseteq Y$ as a subspace, then every continuous function $f: X \to D$ can be extended to a continuous function $\bar{f}: Y \to D$. As a diagram we have:

$$
\begin{gathered}
X \subseteq Y 
X \xrightarrow{f} D 
Y \xrightarrow{\bar{f}} D
\end{gathered}
$$

Some people will object to this terminology because I use the subspace relationship rather than a monomorphism in the category of $T_0$-spaces and continuous maps. However, only the trivial 1-point space is injective in the sense of monomorphisms in that category, and so the notion is uninteresting. If the reader prefers another terminology, I do not mind. As we shall see these spaces have very strong retraction properties.

A slightly less trivial example of an injective space is the 2-point space $\mathbb{O}$ with "points" $\bot$ and $\top$ where $\top$ is open but $\bot$ is not. (This space is sometimes called the *Sierpinski Space*.)

**1.2 Proposition.** The space $\mathbb{O}$ is injective.

**Proof:** As is obvious, the continuous maps $f: X \to \mathbb{O}$ are in a one-one correspondence with the open subsets of $X$ (consider $f^{-1}(\top)$). If $X \subseteq Y$ as a subspace, then an open subset of $X$ is the restriction of some open subset of $Y$. Thus any $f: X \to \mathbb{O}$ can be extended to $\bar{f}: Y \to \mathbb{O}$. $\square$

**1.3 Proposition.** The Cartesian product of any number of injective spaces is injective under the product topology.

**Proof:** The argument is standard. A map into the product can be projected onto each of the factors. Each of these projections can be extended. Then the separate maps can be put together again to make the required extended map into the product. $\square$

We now have a large number of injective spaces, and further examples could be found using the next fact.

**1.4 Proposition.** A retract of an injective space is injective.

**Proof:** Let $D$ be injective. By a retract of $D$ we understand a subspace $D' \subseteq D$ for which there exists a retraction map $j: D \to D'$ such that

$$
D' = x \in D : j(x) = x.
$$

Then if $f: X \to D'$ and $X \subseteq Y$, we have $f: X \to D$ as a continuous map also. Taking $\bar{f}: Y \to D$, we have only to form

$$
j \circ \bar{f} : Y \to D'
$$

to show that $D'$ is injective. $\square$

The relationship between arbitrary $T_0$-spaces and the injective spaces is given by the embedding theorem.

**1.5 Proposition.** Every $T_0$-space can be embedded in an injective space; in fact, in a Cartesian power of the 2-element space $\mathbb{O}$.

**Proof:** The proof is well known (cf. Čech (1966), Theorem 26B.9, p. 484.) But we give the argument for completeness sake. Let $X$ be the given space, and let $\mathfrak{O}$ be the class of open subsets of $X$. Let

$$
D = \mathbb{O}^{\mathfrak{O}}
$$

be the Cartesian power of $\mathbb{O}$. Then $D$ is injective by 1.3. Define the map $e: X \to D$ by:

$$
e(x)(U) = \begin{cases} \top & \text{if } x \in U,  \bot & \text{if } x \notin U, \end{cases}
$$

for $x \in X$ and $U \in \mathfrak{O}$. This map $e$ is continuous in view of the topology given to $\mathbb{O}$ and to $D$. The map $e$ is one-one, because $X$ is $T_0$. Finally, if $U \subseteq X$ is open, then

$$
\begin{aligned}
e(U) &= e(x) : x \in U 
&= e(x) : e(x)(U) = \top 
&= e(X) \cap t \in D : t(U) \in \top,
\end{aligned}
$$

which shows that the image $e(U)$ is open in the subspace $e(X) \subseteq D$. Therefore $e: X \to D$ is an embedding of $X$ as a subspace in $D$. $\square$

**1.6 Corollary.** The injective spaces are exactly the retracts of the Cartesian powers of $\mathbb{O}$.

**Proof:** Such a retract is injective by 1.4. If $D$ is injective, then it is (homeomorphic to) a subspace of a power of $\mathbb{O}$. But since $D$ is injective the identity function on the subspace to itself can be extended to the whole of the power of $\mathbb{O}$ providing the required retraction. $\square$

**1.7 Corollary.** A space is injective iff it is a retract of every space of which it is a subspace.

**Proof:** As in the proof of 1.6, this property is obvious for injective spaces. But in view of 1.5 every such space is a retract of a power of $\mathbb{O}$ and hence is injective. $\square$

As a result of these very elementary considerations, the injective spaces could be called *absolute retracts*, if one remembers to modify the standard definitions by using *arbitrary* subspaces rather than just *closed* subspaces. Note too that it is easy to show that the only continuous maps $e: X \to Y$ for which the extension property

$$
\begin{gathered}
X \xrightarrow{e} Y 
X \xrightarrow{f} \mathbb{O} 
Y \xrightarrow{\bar{f}} \mathbb{O}
\end{gathered}
$$

could hold for *all* continuous $f: X \to \mathbb{O}$ are embeddings as subspaces.

Thus it would seem that we have a reasonably good initial grasp of the notion of injective spaces, but further constructions are considerably facilitated by the introduction of the lattice structure.
