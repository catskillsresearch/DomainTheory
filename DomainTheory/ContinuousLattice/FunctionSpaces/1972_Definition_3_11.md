# Definition 3.11

As a corollary of 3.10 we can easily see which *subspaces* of a continuous lattice $D'$ are projections of it. Such a subspace $D \subseteq D'$ must first be closed under $\bigsqcup$. That is, if $S \subseteq D$, then $\bigsqcup S \in D$ for

all $S$, where the lub is taken in the sense of $D'$. The identity map on $D$ will then satisfy (i) and (ii). But this is not enough, since we would not know that $D$ is a continuous lattice, nor whether (iii) holds. The following additional condition would be sufficient, if assumed for all $y \in D$:

$$y = \bigsqcup x \in D : x \ll y,$$

where $\ll$ is taken in the sense of $D'$. This implies that

$$y = \bigsqcup \sqcap (D \cap U) : y \in U$$

where $U$ ranges over the open subsets of $D'$ and where the $\sqcap$ is taken in the sense of $D$. This condition makes the subspace topology the same as the lattice topology on $D$ and besides makes $D$ continuous, which is just what we need. (Another way to put it is that whenever $z \ll y$, where $y \in D$ but $z \in D'$, then $z \sqsubseteq x \ll y$, for some $x \in D$.)

It seems a bit troublesome to characterize in a simple way just which maps $j : D' \to D$ are projections. (Other than saying outright that the map $i : D \to D'$ such that for all $x \in D$:

$$i(x) = \sqcap x' \in D' : x \sqsubseteq j(x')$$

is the continuous partial inverse to $j$.) But we can say very easily which continuous maps $j : D' \to D'$ are projections onto *subspaces*; namely, we must have

$$j = j \circ j \sqsubseteq \mathrm{id}.$$

The subspace in question then is:

$$D = x \in D' : j(x) = x.$$

This non-empty subspace is the exact range of $j$ and is closed under $\bigsqcup$. Let $y \in D$. Then if $x' \ll y$ in $D'$, we find $j(x') \sqsubseteq x' \ll y$. Thus since

$$y = \bigsqcup x' \in D' : x' \ll y,$$

we see that

$$y = j(y) = \bigsqcup j(x') : x' \ll y.$$

But each $j(x') \in D$, so $y = \bigsqcup x \in D : x \ll y$, as desired.

The foregoing discussion suggests looking more closely at the space of all projections of a continuous lattice since they are so easily characterized.

**3.11 Definition.** Given a continuous lattice $D$, we let the space of projections be denoted by:

$$J_D = j \in [D \to D] : j = j \circ j \sqsubseteq \mathrm{id}.$$
