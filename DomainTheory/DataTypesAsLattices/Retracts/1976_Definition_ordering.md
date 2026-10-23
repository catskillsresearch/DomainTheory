# Definition

We note further that by the embedding theorem (Theorem 1.6), it follows that any separable (by which we mean countably-based) continuous lattice is a retract of $\mathbf{P}\omega$; hence, our universal space is indeed rich in retracts. A very odd point is that $a = a \circ a$ is a fixed-point equation itself ($\lambda u.\, u \circ u$ is obviously continuous). Thus the retraction mappings form a complete lattice. Is this a continuous lattice? Ershov proved that it is not. The argument is below. A related question is solved positively in the next section. Actually the ordering of retracts under $\subseteq$ does not seem to be all that interesting; a more algebraic ordering is given by:

**DEFINITION.** For retracts $a$ and $b$ we write $a \sqsubseteq b$ for $a = a \circ b = b \circ a$.

The idea here should be clear: $a \sqsubseteq b$ means that $a$ is a retract of $b$. It is easy to prove the:

## The space of retracts

Let $\mathbf{RET} = \{a \mid a = a \circ a\}$. Theorem 4.1 makes this a complete lattice. It is not a continuous lattice, because meet on $\mathbf{RET}$ does not preserve directed suprema. The argument is Ershov's.

Call a retract $a$ *nonextensive* when $x \not\subseteq a(x)$ for every nonempty finite $x$, and call a retract $b$ *finite* when $b(\top)$ is finite. A nonextensive retract and a finite retract are orthogonal: their meet is $\bot$. If $c \subseteq a$ and $c \subseteq b$, then $c$ is finite, and $c(x) = c(c(x)) \subseteq a(c(x))$. A nonempty finite value would contradict nonextensiveness, so $c(x) = \bot$.

The finite retracts $b_n = \lambda x.\, e_n$ are directed, and $\bigcup \{b_n \mid n \in \omega\} = \lambda x.\, \top = \top$. If meet preserved that supremum, every nonextensive retract would be $\bot$.

Let $\ll$ be a strict dense linear ordering of $\omega$ of the order type of the rationals, and set

$$a(x) = \{m \mid \exists n \in x.\, m \ll n\}.$$

Transitivity and density make $a$ a retract, irreflexivity makes it nonextensive, and $a(\top) = \top$. So meet on $\mathbf{RET}$ is not continuous. Many such relations exist, and the retracts they determine are distributive. A nondistributive example is

$$a'(x) = \{m \mid \exists n, n' \in x.\, n \ll m \ll n'\}.$$
