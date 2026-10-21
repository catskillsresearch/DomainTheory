# Theorem 1.4

The other general fact about continuous functions that we shall use constantly concerns fixed points, whose existence can be proved using a well-known method.

**THEOREM 1.4** (The fixed-point theorem). *Every continuous function $f : \mathbf{P}\omega \to \mathbf{P}\omega$ has a least fixed point given by the formula:*

$$\mathbf{fix}(f) = \bigcup \{ f^n(\varnothing) \mid n \in \omega \},$$

*where $\varnothing$ is the empty set and $f^n$ is the $n$-fold composition of $f$ with itself.*

Actually **fix** is a *functional* with continuity properties of its own. We shall not give the required definitions here because they can be more easily derived from the construction of the model given in the next section.

For those familiar with the abstract theory of topological spaces we give in conclusion two general facts about continuous functions with values in $\mathbf{P}\omega$ which indicate the scope and generality of our method.

**Lean 4**

- [DataTypesAsLattices/FixedPoint/theorem_1_4.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_4.lean)
