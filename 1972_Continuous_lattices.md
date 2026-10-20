# Continuous lattices

**2. CONTINUOUS LATTICES.** Every $T_0$-space becomes a partially ordered set under the definition:

$$
x \sqsubseteq y \text{ iff whenever } x \in U \text{ and } U \text{ is open, then } y \in U.
$$

Indeed, though this relation is reflexive and transitive, the condition that it be *antisymmetric* is exactly equivalent to the $T_0$-axiom.

In the converse direction, every partially ordered set $\langle X, \sqsubseteq \rangle$ can be so obtained, for we have only to define $U \subseteq X$ as being open if it satisfies the condition:

(i) whenever $x \in U$ and $x \sqsubseteq y$, then $y \in U$.

The axioms for partial order make $X$ a $T_0$-space, because for any $y \in X$ the set

$$
x \in X : x \not\sqsubseteq y
$$

is open. This connection is not very interesting, however.

What *is* interesting in topological spaces is *convergence* and the properties of *limit points*. We shall discuss limits in terms of *nets*, in particular in terms of *monotone nets*. A monotone net in a $T_0$-space $X$ is a function

$$
x : I \to X
$$

where $\langle I, \le \rangle$ is a directed set and where $i \le j$ implies $x_i \sqsubseteq x_j$ for all $i, j \in I$. In a $T_1$-space a monotone net is constant (hence, uninteresting) because the $\sqsubseteq$-relation is the identity. As usual (cf. Kelley (1955), p.66) we say that a net $x$ *converges* to an element $y$ iff whenever $U$ is open and $y \in U$, then for some $i \in I$ we have $x_j \in U$ for all $j \ge i$. Note that a monotone net $x$ converges to each of its terms $x_i$. Suppose that a monotone net $x$ converges to an element $y$ which is an upper bound to all the terms of $x$. Then $y$ must be the *least upper bound*, which we write as:

$$
y = \bigsqcup x_i : i \in I.
$$

To see this, assume that $z$ is any other upper bound with $x_i \sqsubseteq z$ for all $i \in I$. If $U$ is open and $y \in U$, then $x_i \in U$ for some $i \in I$. But then $z \in U$, and so $y \sqsubseteq z$ follows.

We shall find that most of the facts about the topology of the spaces we are concerned with here can be expressed in terms of least upper bounds (lubs). It is not always the case, however, that lubs are limits. Thus, for a partially ordered set $X$, we impose a further restriction on its topology beyond condition (i) for saying when a subset $U$ is open:

(ii) whenever $S \subseteq X$ is *directed*, $\bigsqcup S$ exists, and $\bigsqcup S \in U$, then $S \cap U \neq \emptyset$.

By a directed subset of $X$ we of course mean that it is directed in the sense of the partial ordering $\sqsubseteq$. Note that in this paper directed sets are always *non-empty*. The sets satisfying (i) and (ii) form the *induced topology* on a partially ordered set $X$, which is still a $T_0$-space because the sets $x \in X : x \not\sqsubseteq y$ remain open even in the sense of (ii). Obviously a directed set $S \subseteq X$ can be regarded as a net, and now in view of (ii) it follows that $S$ converges to $\bigsqcup S$ — if this lub exists. We can summarize this discussion as follows.

**2.1 Proposition.** *In a partially ordered set $X$ with the induced topology, a monotone net $x : I \to X$ with a least upper bound converges to an element $y \in X$ iff*

$$
y \sqsubseteq \bigsqcup x_i : i \in I.
$$

$\square$

Our main interest will lie with those partially ordered sets in which every subset has a lub: namely, *complete lattices*. If $D$ is such a space we write $\bot = \bigsqcup \emptyset$ and $\top = \bigsqcup D$ for the smallest and largest elements (read: bottom and top). As is well known, greatest lower bounds must exist, for:

$$
\sqcap S = \bigsqcup x \in D : x \sqsubseteq y \text{ for all } y \in S
$$

gives the definition.

Given a complete lattice $D$ we define

$$
x \ll y \text{ iff } y \in \text{Int}z \in D : x \sqsubseteq z,
$$

where the interior is taken in the sense of the induced topology. The relation $x \ll y$ behaves somewhat like a strict ordering relation; at least its meaning is clearly that $y$ should be definitely larger than $x$ in the partial ordering. Such a relation has many pleasant properties.

The primary purpose of introducing it is to provide a simple definition for the kind of spaces that are most useful to us. We first mention the most elementary features of this relation.

**2.2 Proposition.** In a complete lattice $D$ we have:

(i) $\bot \ll x$;

(ii) $x \ll z$ and $y \ll z$ imply $x \sqcup y \ll z$;

(iii) $x \ll y \sqsubseteq z$ implies $x \ll z$;

(iv) $x \sqsubseteq y \ll z$ implies $x \ll z$;

(v) $x \ll y$ implies $x \sqsubseteq y$;

(vi) $x \ll x$ iff $z \in D : x \sqsubseteq z$ is open;

(vii) if $S \subseteq D$ is directed, then $x \ll \bigsqcup S$ iff $x \ll y$ for some $y \in S$. $\square$

The proofs of these statements can be safely left to the reader.

**2.3 Definition.** A *continuous lattice* is a complete lattice $D$ in which for every $y \in D$ we have:

$$
y = \bigsqcup x \in D : x \ll y.
$$

As an alternate definition we find:

**2.4 Proposition.** A complete lattice $D$ is continuous iff for every $y \in D$ we have:

$$
y = \bigsqcup \sqcap U : y \in U,
$$

where $U$ ranges over the open subsets of $D$.

**Proof:** Suppose $D$ is continuous. If $y \in D$ and $x \ll y$, then let $U = \text{Int}z : x \sqsubseteq z$, an open set. Now $y \in U$ by definition, and $U \subseteq z : x \sqsubseteq z$. Thus,

$$
x \sqsubseteq \sqcap U \sqsubseteq y.
$$

It easily follows by lattice theory that the equation of 2.3 implies that of 2.4.

In the converse direction we have only to note that if $U$ is open and $y \in U$, then $\sqcap U \ll y$. The implication from 2.4 to 2.3 results at once. $\square$

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

**2.6 Proposition.** *With functions from complete lattices to complete lattices, a function of several variables is continuous in the variables jointly iff it is continuous in the variables separately.*

**Proof:** It will be sufficient to discuss functions of two variables. The product $D \times D'$ of two complete lattices is a complete lattice, and it is easy to check that the induced topology is the product topology. Since projection is continuous, joint continuity implies separate continuity. To check the converse suppose that

$$
f : D \times D' \to D''
$$

is a map where the separate continuity holds as follows:

$$
f(\bigsqcup S, y) = \bigsqcup f(x, y) : x \in S
$$

and

$$
f(x, \bigsqcup S') = \bigsqcup f(x, y) : y \in S'
$$

where $S \subseteq D$ and $S' \subseteq D'$ are directed and $x \in D$ and $y \in D'$. Let now

$$
S^* \subseteq D \times D'
$$

be directed in the product. The projection of $S^*$ to $D$ and of $S^*$ to $D'$ produces directed subsets $S \subseteq D$ and $S' \subseteq D'$. Note that

$$
\bigsqcup S^* = (\bigsqcup S, \bigsqcup S').
$$

Thus by assumption

$$
f(\bigsqcup S^*) = \bigsqcup f(x, y) : x \in S, y \in S'.
$$

But since $S^*$ is directed, $x \in S$ and $y \in S'$ implies $x \sqsubseteq u$ and $y \sqsubseteq v$ for $(u, v) \in S^*$. Thus by monotonicity of $f$ we can show

$$
f(\bigsqcup S^*) = \bigsqcup f(u, v) : (u, v) \in S^*
$$

and that gives the joint continuity. $\square$

One of the justifications (by euphony at least) of the term *continuous lattice* is the fact that such spaces allow for so many continuous functions. One indication of this is the result:

**2.7 Proposition.** *In a continuous lattice $D$ the finitary lattice operations $\sqcup$ and $\sqcap$ are continuous.*

**Proof:** It is trivial to show that $\sqcup$ is continuous in every complete lattice; this is not so for $\sqcap$. In view of 2.6 we need only show

$$
x \sqcap \bigsqcup S = \bigsqcup x \sqcap y : y \in S
$$

for every directed $S \subseteq D$. In fact it is enough to show

$$
x \sqcap \bigsqcup S \sqsubseteq \bigsqcup x \sqcap y : y \in S
$$

because the opposite inequality is valid in all complete lattices. In view of the fact that $D$ is continuous, it is enough to show that

$$
t \ll x \sqcap \bigsqcup S \text{ implies } t \sqsubseteq \bigsqcup x \sqcap y : y \in S.
$$

So assume $t \ll x \sqcap \bigsqcup S$. Then $t \sqsubseteq x \sqcap \bigsqcup S \sqsubseteq x$. Also $t \ll \bigsqcup S$ because $x \sqcap \bigsqcup S \sqsubseteq \bigsqcup S$. Thus $t \ll y$ for some $y \in S$ since the set

$$
z \in D : t \ll z
$$

is open. But then $t \sqsubseteq y$, and so $t \sqsubseteq x \sqcap y$, and the result follows. $\square$

It is now time to provide some examples of continuous lattices.

**2.8 Proposition.** A finite lattice is a continuous lattice. $\square$

**2.9 Proposition.** The Cartesian product of any number of continuous lattices is a continuous lattice with the induced topology agreeing with the product topology.

**2.10 Proposition.** A retract of a continuous lattice is a continuous lattice with the subspace topology agreeing with the induced topology.

It would seem that the continuous lattices are starting to sound suspiciously like the injective spaces. Indeed, if we can prove the following, the circle will be complete.

**2.11 Proposition.** Every continuous lattice is an injective space under its induced topology.

**2.12 Theorem.** The injective spaces are exactly the continuous lattices.

This theorem is an immediate consequence of the preceding results: an injective space is a retract of a power of $\mathbb{O}$. But $\mathbb{O}$ is a finite lattice $(\perp \sqsubseteq \top)$, and so the given space is a continuous lattice under its induced topology. On the other hand a continuous lattice is injective. It remains then to prove 2.9–2.11.

**Proof of 2.9**

Let $D_i$ for $i \in I$ be a system of continuous lattices. The product

$$
D^* = \prod_{i \in I} D_i
$$

is a complete lattice in the usual way and has its induced topology. Suppose $y \in D^*$ and let $i \in I$. Then $y_i \in D_i$. Since $D_i$ is a continuous lattice

$$
y_i = \bigsqcup x \in D_i : x \ll y_i.
$$

For $x \in D_i$, let $[x]^i \in D^*$ be defined by:

$$
[x]^i_j = \begin{cases} x & \text{if } i = j,  \perp & \text{if } i \neq j. \end{cases}
$$

Note that since $D_i$ is continuous we have:

$$
[y_i]^i = \bigsqcup [x]^i : x \ll y_i,
$$

and

$$
y = \bigsqcup [y_i]^i : i \in I.
$$

It follows that

$$
y = \bigsqcup \bigcap \{ z : z_i \in U \text{ for all } i \in I,\, y_i \in U \},
$$

where $i$ ranges over $I$ and $U$ over the open subsets of $D_i$, because

$$
[x]^i \sqsubseteq \bigcap  z : z_i \in U , \quad \text{where } U =  u \in D_i : x \ll u .
$$

But the sets $ z : z_i \in U $ are open in the product sense, and so

$$
y = \bigsqcup  \bigcap U : y \in U ,
$$

where $U$ ranges now over the open subsets of the product topology on $D^*$. By the remark following 2.4 we conclude that $D^*$ is continuous with the lattice-induced topology being the product topology. $\square$

**Proof of 2.10**

Let $D'$ be a continuous lattice and let $D \subseteq D'$ be a subspace which is a retract. We have for a suitable $j : D' \to D$,

$$
D =  x \in D' : j(x) = x ,
$$

where of course $j$ is continuous.

*First a note of warning:* though $D$ is a subspace it is not a sublattice; that is, the partial ordering on $D$ is the restriction of that of $D'$, but the lubs of $D$ are not those of $D'$. We shall have to distinguish operations by adding a prime ($'$) for those of $D'$.

Suppose $x, y \in D$. Let $z' = x \sqcup y \in D'$ (join taken in $D'$) and define $z = j(z') \in D$. Now $x \sqsubseteq z'$ and $y \sqsubseteq z'$, and $j$ is monotonic, so $x \sqsubseteq z$ and $y \sqsubseteq z$. Suppose $x \sqsubseteq w$ and $y \sqsubseteq w$ with $w \in D$. Then in $D'$ we have $x \sqcup y \sqsubseteq w$; so $z \sqsubseteq w$ also. Hence we have shown that $z = x \sqcup y$ in $D$.

To show that $D$ has a least element $\bot$ (which may be larger than the $\bot' \in D'$), we need a well-known lemma about monotonic functions: Every monotonic function on a complete lattice into itself has a least fixed point. (Cf. Birkhoff (1970), p. 115.) In our case $j$ is monotonic and

$$
\bot = \sqcap \ x \in D' : j(x) \sqsubseteq x
$$

is the desired element in $D$.

Thus $D$ is at least a semilattice with $\bot$ and $\sqcup$. To show that $D$ is a lattice we need to show that every directed $S \subseteq D$ has a lub in $D$. Now we know ($S' = S$, join taken in the ambient lattice $D'$):

$$
\bigsqcup S' \in D',
$$

and this is a limit of a monotone net. So by 2.1, and the continuity of $j$:

$$
\begin{aligned}
j(\bigsqcup S') &= \bigsqcup  j(x) : x \in S  
&= \bigsqcup S
\end{aligned}
$$

in $D$. In this way we now know that $D$ is a complete lattice. We must

still show that $D$ is continuous.

Suppose $y \in D$. In $D'$ we can write:

$$y = \bigsqcup  x \in D' : x \ll y '$$

and this is the limit of a monotone net. Thus

$$j(y) = y = \bigsqcup  j(x) : x \ll y, x \in D' ,$$

where the lub is taken in $D$. Note that the sets

$$U =  z \in D : x \ll z $$

are open in $D$ for each $x \in D'$. Note too that if $z \in U$, then $x \sqsubseteq z$ and so $j(x) \sqsubseteq j(z) = z$. This means that

$$j(x) \sqsubseteq \sqcap U$$

in $D$. We can then write in $D$:

$$y = \bigsqcup \sqcap U : y \in U $$

where $U$ ranges over the open subsets of $D$, and so the lattice is continuous by 2.4. Inasmuch as the open sets $U$ just used were open in the subspace topology, it follows by the remark after 2.4 that the subspace and the lattice-induced topologies coincide. $\square$

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

The lattice approach to injective spaces gives a completely "internal" characterization of them: in the first place the lattices are complete. Next we can define lattice theoretically:

$$
x \ll y \quad \text{iff} \quad \text{whenever } y \sqsubseteq \bigsqcup Z \text{ and } Z \subseteq D \text{ is directed,}
$$

then $x \sqsubseteq z$ for some $z \in Z$.

Finally we assume that for all $y \in D$:

$$y = \bigsqcup  x \in D : x \ll y .$$

That makes $D$ a continuous lattice with the sets $ y \in D : x \ll y $ as a basis for the topology. Such $T_0$-spaces are injective and every injective space can be obtained in this way with the lattice structure being uniquely determined by the topology. Furthermore, as we have seen, the injective property can be exhibited, as in the proof of 2.11, by an explicit formula for extending functions.

The retract approach to injective spaces should also be considered. The Cartesian powers $\mathbb{O}^I$ are very simple spaces; indeed, as lattices these are just the Boolean algebras of *all subsets* of $I$ (that is, isomorphic thereto). The topology has as a basis the

classes of sets containing given finite sets (the *weak topology*, cf. Nerode (1959)). A continuous function

$$j : \mathcal{P}I \to \mathcal{P}I$$

is one of "finite character" so that

$$j(X) = \bigcup  j(F) : F \subseteq X $$

where $X \subseteq I$ and $F$ ranges over *finite sets*. Such a function $j$ is a *retraction* iff it is an *idempotent*:

$$j \circ j = j,$$

which means that the range of $j$ is the set of fixed points of $j$. As we have seen

$$D =  X \in \mathcal{P}I : j(X) = X $$

is a continuous lattice (under $\subseteq$ in this case), and *every* continuous lattice is isomorphic to one obtained in this way. This provides a representation theorem of sorts for continuous lattices, but it does not seem to be of too much help in proving theorems.

The reader should not forget that any space (any *given* number of spaces $X$, $Y$, $\ldots$) can be found as a *subspace* of a continuous lattice $D$. Since $D$ is injective any continuous function $f : X \to Y$ can be extended to a continuous function $\bar{f} : D \to D$. Thus the continuous functions from $D$ into $D$ are a rich totality including *all* the structure of continuous functions on *all* the subspaces. And this remark brings us to the study of function spaces.
