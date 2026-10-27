# Theorem 7.4

**THEOREM 7.4.** If $\mathcal{D}_0$ and $\mathcal{D}_1$ are effectively given, then so are $(\mathcal{D}_0 + \mathcal{D}_1)$ and $(\mathcal{D}_0 \times \mathcal{D}_1)$.

Moreover the combinators $\mathrm{in}_i$ and $\mathrm{out}_i$ and $\mathrm{proj}_i^2$ are all computable; further, if $f$ and $g$ are computable maps, then so are $f + g$ and $f \times g$.

*Proof:* Let the computable presentations be given as:

$$\mathcal{D}_i = \{ X_n^i \mid n \in \mathbf{N} \}.$$

We can assume that the sets of tokens $\Delta_0$ and $\Delta_1$ are disjoint and $\emptyset \notin \mathcal{D}_i$. Then the construction of the sum is just

$$\mathcal{D}_0 + \mathcal{D}_1 = \{ \Delta_0 \cup \Delta_1 \} \cup \mathcal{D}_0 \cup \mathcal{D}_1.$$

As an enumeration we define for $n \in \mathbf{N}$:

$$Z_0 = \Delta_0 \cup \Delta_1 \ ; \ Z_{2n+1} = X_n^0 \ ; \ Z_{2n+2} = X_n^1 \ .$$

We leave as an exercise the check of 7.1(i)–(ii).

For the product we want:

$$\mathcal{D}_0 \times \mathcal{D}_1 = \{ X_n^0 \cup X_m^1 \mid n, m \in \mathbf{N} \}.$$

What we then need are recursive functions $p : \mathbf{N} \to \mathbf{N}$, $q : \mathbf{N} \to \mathbf{N}$, and $r : \mathbf{N} \times \mathbf{N} \to \mathbf{N}$ where for $m, n, k \in \mathbf{N}$ we have:

$$p(r(n, m)) = n \text{ and } q(r(n, m)) = m, \text{ and } r(p(k), q(k)) = k.$$

Thus $r$ is a "one-one pairing function"; there are many ways to find such functions (see Exercise 5.13). We can then define for $k \in \mathbf{N}$:

$$W_k = X_{p(k)}^0 \cup X_{q(k)}^1 \ .$$

Again we leave as an exercise the check that this provides a computable presentation of $\mathcal{D}_0 \times \mathcal{D}_1$.

As for the combinators, the neighbourhood relations have to be worked out in terms of the indices. For example

$$X_n^0 \ \mathrm{in}_0 \ Z_m \text{ iff either } m = 0 \text{ or for some } k$$

$$m = 2k + 1 \text{ and } X_n^0 \subseteq X_k^0 \ .$$

and

$$W_k \ \mathrm{proj}_1^2 \ X_m^1 \text{ iff } X_{q(k)}^1 \subseteq X_m^1 \ .$$

The reader needs to check that these are recursively enumerable

<!-- page 121 -->

Relations in the indices. For this purpose it may be convenient to recall some closure properties of these relations: taking conjunctions, disjunctions, substituting recursive functions, applying an existential quantifier to the front. $\square$

Products give us a way of providing an immediate meaning to the notion of a computable function of several variables. Note that the proof of 3.7 is “effective” and shows that substitution of computable functions of several variables into each other always gives computable functions. We turn next to the function spaces.

**[Theorem_7_4.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem_7_4.lean)**

@import "Theorem_7_4.lean"
