# Proposition 2.5

What is the idea of this definition? A continuous lattice is more special than a complete lattice: not only are lubs to be limits but every element must be a limit from below. This rather rough remark can be made more precise. In any complete lattice $D$ define the *principal limit* of a net $x : I \to D$ by the formula:

$$
\lim \langle x_i : i \in I \rangle = \bigsqcup \sqcap  x_j : j \ge i  : i \in I .
$$

Then specify that $x$ converges to $y \in D$ iff

$$
y \sqsubseteq \lim \langle x_i : i \in I \rangle.
$$

Having a notion of convergence, we can then say that $U \subseteq D$ is open iff every net converging to an element of $U$ is eventually in $U$. This gives nothing more than what we have called the induced topology above, as is easily checked. But now being in possession of a topology, we can redefine convergence in the usual way. Question: when do the two notions of convergence agree? Answer: if and only if $D$ is a continuous lattice.

For obviously by construction the limit definition of convergence implies the topological. Now if $D$ is a continuous lattice and $x$ converges to $y$ topologically, consider an open $U \subseteq D$ with $y \in U$. For some $i \in I$ we shall have $x_j \in U$ for all $j \ge i$. Therefore

$$
\sqcap U \sqsubseteq \sqcap  x_j : j \ge i  \sqsubseteq \lim \langle x_i : i \in I \rangle.
$$

From the formula of 2.4 it at once follows that $y \sqsubseteq \lim \langle x_i : i \in I \rangle$. Thus, in continuous lattices, we have shown that the two notions of convergence are the same.

Finally, suppose that the two notions coincide for a complete lattice $D$. Define a directed set $I = (U, z) : y, z \in U$, where $z$ ranges over $D$ and $U$ over open subsets of $D$. This set is directed by the relation: $(U, z) \le (V, w)$ iff $U \supseteq V$. Let $x : I \to D$ be given by: $x(U, z) = z$. Then $x$ is a net converging to $y$ topologically. But

$$
\lim \langle x_i : i \in I \rangle = \bigsqcup \sqcap U : y \in U.
$$

In this way we see that the assumption about the two styles of convergence implies that $D$ is a continuous lattice in view of 2.4.

In $T_0$-spaces continuous functions are always monotonic (i.e. $\sqsubseteq$-preserving). For continuous lattices, by virtue of the remarks we have just made about limits, we can define the continuity of $f : D \to D'$ to mean that

$$
f(\lim \langle x_i : i \in I \rangle) \sqsubseteq \lim' \langle f(x_i) : i \in I \rangle
$$

for all nets $x : I \to D$. This is all very fine, but general limits are messy to work with; we shall find it easier to state results in terms of lubs as in 2.5–2.7 below.

Before going any deeper, however, we should clear up another point about topologies. Suppose that $D$ is any $T_0$-space which becomes a complete lattice under its induced partial ordering. Then it is evident from our definitions that every set open in the given topology is also open in the topology induced from the lattice structure. Question: when do the two topologies agree? Answer: a sufficient condition is that the equation:

$$
y = \bigsqcup \sqcap U : y \in U
$$

hold for all $y \in D$, where $U$ ranges over the given open sets. Because in that case if $V$ is open in the lattice sense and $y \in V$, then $\sqcap U \in V$ for some set $U$, open in the given sense, where $y \in U$. But $U \subseteq V$ follows, and so $V$ is a union of given open sets and is itself open in the given topology. Of course this equation implies that $D$ is a continuous lattice by virtue of 2.4. Notice that by the same token the sets of the form $y \in D : x \ll y$ will form a basis for the open sets of a continuous lattice.

hold for all $y \in D$, where $U$ ranges over the given open sets. Because in that case if $V$ is open in the lattice sense and $y \in V$, then $\sqcap U \in V$ for some set $U$, open in the given sense, where $y \in U$. But $U \subseteq V$ follows, and so $V$ is a union of given open sets and is itself open in the given topology. Of course this equation implies that $D$ is a continuous lattice by virtue of 2.4. Notice that by the same token the sets of the form $y \in D : x \ll y$ will form a basis for the open sets of a continuous lattice.

**2.5 Proposition.** *If $D$ and $D'$ are complete lattices with their induced topologies, then a function $f : D \to D'$ is continuous iff for all directed subsets $S \subseteq D$:*

$$
f(\bigsqcup S) = \bigsqcup f(x) : x \in S.
$$

**Proof:** If $f : D \to D'$ is continuous, the equation follows from the definition of continuous function and the fact that lubs are limits. Assume then that the equation holds for all directed sets $S$. Let $U' \subseteq D'$ be open in $D'$ and let

$$
U = x \in D : f(x) \in U'.
$$

We must show that $U$ is open in $D$. Note first that if $x \sqsubseteq y$, then $S = x, y$ is directed; hence,

$$
f(x \sqcup y) = f(y) = f(x) \sqcup f(y),
$$

so $f(x) \sqsubseteq f(y)$. Thus $f$ is monotonic and so $U$ satisfies condition (i). That $U$ satisfies condition (ii) follows at once from the above equation. $\square$

**Lean 4**

- [ContinuousLattice/ScottMaps/PreservesDirectedSup.lean](PreservesDirectedSup.lean)
- [ContinuousLattice/ScottMaps/preservesDirectedSup_monotone.lean](preservesDirectedSup_monotone.lean)
- [ContinuousLattice/ScottMaps/scottOpen_preimage.lean](scottOpen_preimage.lean)
- [ContinuousLattice/ScottMaps/continuous_preservesDirectedSup.lean](continuous_preservesDirectedSup.lean)
- [ContinuousLattice/ScottMaps/continuous_of_preservesDirectedSup.lean](continuous_of_preservesDirectedSup.lean)
- [ContinuousLattice/ScottMaps/proposition_2_5.lean](proposition_2_5.lean)
- [ContinuousLattice/WayBelow/exists_wayBelow_subset.lean](../WayBelow/exists_wayBelow_subset.lean)
- [ContinuousLattice/WayBelow/exists_wayBelow_Ici_subset.lean](../WayBelow/exists_wayBelow_Ici_subset.lean)
