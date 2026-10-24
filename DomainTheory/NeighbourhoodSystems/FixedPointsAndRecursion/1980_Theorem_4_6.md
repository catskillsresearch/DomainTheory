# Theorem 4.6

## Human-English

**THEOREM 4.6.** All models of Peano's Axioms are isomorphic.

*Proof:* There are several ways to give the proof, but, for the sake of illustration, an application of the fixed-point theorem is appropriate here. Let $\langle \mathbf{N}, 0, {}^+ \rangle$ be one model, and let $\langle \mathbf{M}, \square, {}^\# \rangle$ be another. Let $\mathbf{N} \times \mathbf{M}$ be the ordinary cartesian product of the two sets and let

$$
P(\mathbf{N} \times \mathbf{M})
$$

be the powerset (set of all subsets) of $\mathbf{N} \times \mathbf{N}$. As in Exercises 1.15 and 2.20, we regard this set of elements as a domain, whose finite elements are just the finite subsets of the given set $\mathbf{N} \times \mathbf{M}$. The following mapping on $u \subseteq \mathbf{N} \times \mathbf{M}$ is easily proved approximable:

$$
u \mapsto \{(0, \square)\} \cup \{(n^+, m^\#) \mid (n, m) \in u\}.
$$

(This assertion should be checked as an exercise.) We thus let $r$ be the (least) fixed point:

$$
r = \{(0, \square)\} \cup \{(n^+, m^\#) \mid (n, m) \in r\}.
$$

<!-- page 66 -->

This $r \subseteq \mathbf{N} \times \mathbf{M}$ as a binary relation will turn out to be a one-one correspondence giving the required isomorphism.

First of all we see by construction that

(i) $0 \ r \ \square$;

(ii) $n \ r \ m$ implies $n^+ \ r \ m^\#$.

So, if $r$ proves to be a one-one correspondence, it will then be the desired isomorphism. Now, the two sets shown in the equation

$$
\{(0, \square)\} \cap \{(n^+, m^\#) \mid (n, m) \in r\} = \emptyset
$$

are disjoint by virtue of axiom 4.5(i). Therefore, $0$ in $\mathbf{N}$ corresponds by $r$ to one and only one element of $\mathbf{M}$, namely the element $\square$. Let $x \subseteq \mathbf{N}$ be the set of all elements of $\mathbf{N}$ corresponding by $r$ to a unique element of $\mathbf{M}$. We have just shown $0 \in x$. Suppose $n \in x$, and let $m \in \mathbf{M}$ be the unique element with $n \ r \ m$. Now $n^+ \ r \ m^\#$ holds, so $n^+$ corresponds to at least one element of $\mathbf{M}$. If $n^+ \ r \ k$ also holds, then since $(n^+, k) \neq (0, \square)$, the fixed-point equation implies

$$
n^+ = n_0^+ \quad \text{and} \quad k = m_0^\#
$$

for some $(n_0, m_0) \in r$. By axiom 4.5(ii), $n = n_0$, and, by uniqueness (remember $n \in x$), $m = m_0$; thus, $m^\#$ is the unique correspondent for $n^+$. We have proved $n^+ \in x$. Therefore, $x^+ \subseteq x$; so by axiom 4.5(iii), $x = \mathbf{N}$ holds. Otherwise said, every element in $\mathbf{N}$ corresponds to a unique element of $\mathbf{M}$.

Note that the rôles of $\mathbf{N}$ and $\mathbf{M}$ are completely symmetric, *and* they satisfy the same axioms as structured sets. It follows, then, that every element of $\mathbf{M}$ corresponds to a unique element of $\mathbf{N}$. The proof that $r$ is a one-one correspondence is now complete. $\square$

## AI: Human-English to AI-Lean

**[Theorem_4_6.lean](Theorem_4_6.lean)**

@import "Theorem_4_6.lean"
