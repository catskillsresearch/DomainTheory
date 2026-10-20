# Continuous functions

The domain $\mathbf{P}\omega$ of all subsets of the set $\omega$ of nonnegative integers is a complete lattice under the partial ordering $\subseteq$ of set inclusion, as is well known. We use the usual symbols $\cup$, $\cap$, $\bigcup$, $\bigcap$ for the finite and infinite lattice operations of union and intersection. $\mathbf{P}\omega$ is of course also a Boolean algebra; and for complements we write

$$\sim x = \{ n \mid n \notin x \}$$

where it is understood that such variables as $i, j, k, l, m, n$ range over *integers in* $\omega$, while $u, v, w, x, y, z$ range over *subsets of* $\omega$.

The domain $\mathbf{P}\omega$ can also be made into a topological space—in many ways. A common method is to match each $x \subseteq \omega$ with the corresponding characteristic function in $\{0, 1\}^\omega$, and to take the induced product topology. In this way $\mathbf{P}\omega$ is a totally disconnected compact Hausdorff space homeomorphic to the Cantor “middle-third” set. This is *not* the topology we want; it is a *positive-and-negative* topology which makes the function $\sim x$ continuous. We want a weaker topology: the topology of positive “information”, which has the advantage that all continuous functions possess fixed points. (The equation $x = \sim x$ is impossible.) The topology that we *do* want is exactly that appropriate to considering $\mathbf{P}\omega$ to be a continuous lattice. But all this terminology of abstract mathematics is quite unnecessary, since the required definitions can be given in very elementary terms.

To make the topology “visible”, we introduce a standard enumeration $\{e_n \mid n \in \omega\}$ of all *finite* subsets of $\omega$. Specifically we set

$$e_n = \{k_0, k_1, \cdots, k_{m-1}\},$$

provided that $k_0 < k_1 < \cdots < k_{m-1}$ and $n = \sum_{i < m} 2^{k_i}$. Thus $n$ is the code number for $e_n$, and the elements of $e_n$ are the exponents in the binary expansion of the integer $n$. This is a one-to-one enumeration of finite subsets, where $k \in e_n$ always implies $k < n$, the function $\max(e_n)$ is (primitive) recursive in $n$, and the relations $k \in e_n$, $e_n \subseteq e_m$, $e_n = e_m \cup e_k$ are all (primitive) recursive in $k, m, n$.

Topologically speaking the finite sets $e_n$ are *dense* in the space $\mathbf{P}\omega$, for each $x \in \mathbf{P}\omega$ is the “limit” of its finite subsets in the sense that

$$x = \bigcup \{e_n \mid e_n \subseteq x\}.$$

To make this precise we need a rigorous definition of *open subset* of $\mathbf{P}\omega$.

**DEFINITION.** A *basis* for the neighborhoods of $\mathbf{P}\omega$ consists of those sets of the form:

$$\{x \in \mathbf{P}\omega \mid e_n \subseteq x\},$$

for a given $e_n$. An arbitrary *open subset* is then a union of basic neighborhoods.

It is easy to prove that an open subset $U \subseteq \mathbf{P}\omega$ is just a set of “finite character”; that is, a set such that for all $x \in \mathbf{P}\omega$ we have $x \in U$ if and only if some finite subset of $x$ also belongs to $U$. An alternate approach would define directly what we mean by a continuous function using the idea that such functions must preserve limits.

**DEFINITION.** A function $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is *continuous* iff for all $x \in \mathbf{P}\omega$ we have:

$$f(x) = \bigcup \{f(e_n) \mid e_n \subseteq x\}.$$

Again it is an easy exercise to prove that a function is continuous in the sense of this definition iff it is continuous in the usual topological sense (namely: inverse images of open sets are open). For giving proofs it is even more convenient to have the usual $\varepsilon$-$\delta$ formulation of continuity.

**THEOREM 1.1** (The characterization theorem). A function $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is *continuous* iff for all $x \in \mathbf{P}\omega$ and all $e_m$ we have:

$$e_m \subseteq f(x) \quad \text{iff} \quad \exists e_n \subseteq x.\; e_m \subseteq f(e_n).$$

Note that open sets and continuous functions have a *monotonicity property*:

*whenever* $x \subseteq y$ *and* $x \in U$, *then* $y \in U$; *and*

*whenever* $x \subseteq y$, *then* $f(x) \subseteq f(y)$.

This gives a precise expression to the “positive” character of our topology. However, note too that openness and continuity mean rather more than just monotonicity. In particular, a continuous function is completely determined by the pairs of integers $n, m$ such that $m \in f(e_n)$, as can be seen from the definition. (Hence, there are only a continuum number of continuous functions, but more than a continuum number of monotonic functions.) This brings us to the definition of the *graph* of a continuous function.

To formulate the definition, we introduce a standard enumeration $(n, m)$ of all pairs of integers. Specifically we set

$$(n, m) = \tfrac{1}{2}(n + m)(n + m + 1) + m.$$

This is the enumeration along the “little diagonals” going from left to right, and it produces the ordering:

$$(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2), (3, 0), (2, 1), \dots.$$

Note that $n \leq (n, m)$ and $m \leq (n, m)$ with equality possible only in the cases of $(0, 0)$ and $(1, 0)$. This is a one-to-one enumeration, and the inverse functions are (primitive) recursive—but we do not require at the present any notation for them.

**DEFINITION.** The graph of a continuous function $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is defined by the equation:

$$\mathbf{graph}(f) = \{ (n, m) \mid m \in f(e_n) \};$$

while the function determined by any set $u \subseteq \omega$ is defined by the equation:

$$\mathbf{fun}(u)(x) = \{ m \mid \exists e_n \subseteq x.\; (n, m) \in u \}.$$

**THEOREM 1.2** (The graph theorem). *Every continuous function is uniquely determined by its graph in the sense that:*

(i) $\mathbf{fun}(\mathbf{graph}(f)) = f.$

*Conversely, every set of integers determines a continuous function and we have:*

(ii) $u \subseteq \mathbf{graph}(\mathbf{fun}(u)),$

*where equality holds just in case $u$ satisfies:*

(iii) *whenever $(k, m) \in u$ and $e_k \subseteq e_n$, then $(n, m) \in u$.*

Besides functions of one variable we need to consider also functions of several variables. The official definition for one variable given above can be extended simply by saying $f(x, y, \dots)$ is continuous iff it is continuous in each of $x, y, \dots$. Those familiar with the product topology can prove that for our special positive topology on $\mathbf{P}\omega$ this is equivalent to being continuous on the product space (continuous in the variables jointly). Those interested only in elementary proofs can calculate out directly from the definition (with the aid of 1.1) that continuity behaves under combinations by substitution [as in: $f(g(x, y), h(y, x, y))$].

**THEOREM 1.3** (The substitution theorem). *Continuous functions of several variables on $\mathbf{P}\omega$ are closed under substitution.*

The other general fact about continuous functions that we shall use constantly concerns fixed points, whose existence can be proved using a well-known method.

**THEOREM 1.4** (The fixed-point theorem). *Every continuous function $f : \mathbf{P}\omega \to \mathbf{P}\omega$ has a least fixed point given by the formula:*

$$\mathbf{fix}(f) = \bigcup \{ f^n(\varnothing) \mid n \in \omega \},$$

*where $\varnothing$ is the empty set and $f^n$ is the $n$-fold composition of $f$ with itself.*

Actually **fix** is a *functional* with continuity properties of its own. We shall not give the required definitions here because they can be more easily derived from the construction of the model given in the next section.

For those familiar with the abstract theory of topological spaces we give in conclusion two general facts about continuous functions with values in $\mathbf{P}\omega$ which indicate the scope and generality of our method.

**THEOREM 1.5** (The extension theorem). *Let $X$ and $Y$ be arbitrary topological spaces where $X \subseteq Y$ as a subspace. Then every continuous function $f : X \to \mathbf{P}\omega$ can be extended to a continuous function $\bar{f} : Y \to \mathbf{P}\omega$ defined by the equation:*

$$\bar{f}(y) = \bigcup \{ \bigcap \{ f(x) \mid x \in X \cap U \} \mid y \in U \},$$

*where $y \in Y$, and $U$ ranges over the open subsets of $Y$.*

**THEOREM 1.6** (The embedding theorem). *Every $T_0$-space $X$ with a countable basis $\{U_n \mid n \in \omega\}$ for its topology can be embedded in $\mathbf{P}\omega$ by the continuous function $\varepsilon : X \to \mathbf{P}\omega$ defined by the equation:*

$$\varepsilon(x) = \{ n \mid x \in U_n \}.$$

Technically the $T_0$-hypothesis is what is needed to show that $\varepsilon$ is one-to-one. The upshot of these two theorems is that in looking for (reasonable) topological structures we can confine attention to the subspaces of $\mathbf{P}\omega$ and to continuous functions defined on *all* of $\mathbf{P}\omega$. Thus the emphasis on a single space is justified structurally. What we shall see in the remainder of this work is that the use of a single space is also justified practically because the required subspaces and functions can be *defined* in very simple ways by a natural method of equations.

In order to make the plan of the work clearer, the proofs of the theorems have been placed in an Appendix when they are more than simple exercises.

**Lean 4**

- [DataTypesAsLattices/Continuous.lean](DomainTheory/DataTypesAsLattices/Continuous.lean)
- [DataTypesAsLattices/Continuous/Basic.lean](DomainTheory/DataTypesAsLattices/Continuous/Basic.lean)
- [DataTypesAsLattices/Continuous/IsScottContinuous.lean](DomainTheory/DataTypesAsLattices/Continuous/IsScottContinuous.lean)
- [DataTypesAsLattices/Continuous/IsScottOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/IsScottOpen.lean)
- [DataTypesAsLattices/Continuous/basicNhhd.lean](DomainTheory/DataTypesAsLattices/Continuous/basicNhhd.lean)
- [DataTypesAsLattices/Continuous/basicNhhd_eq_iInter.lean](DomainTheory/DataTypesAsLattices/Continuous/basicNhhd_eq_iInter.lean)
- [DataTypesAsLattices/Continuous/basicNhhd_inter.lean](DomainTheory/DataTypesAsLattices/Continuous/basicNhhd_inter.lean)
- [DataTypesAsLattices/Continuous/basicNhhd_zero.lean](DomainTheory/DataTypesAsLattices/Continuous/basicNhhd_zero.lean)
- [DataTypesAsLattices/Continuous/exists_basicNhhd_subset_of_generateOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/exists_basicNhhd_subset_of_generateOpen.lean)
- [DataTypesAsLattices/Continuous/exists_e_cover_finite.lean](DomainTheory/DataTypesAsLattices/Continuous/exists_e_cover_finite.lean)
- [DataTypesAsLattices/Continuous/isOpen_basicNhhd.lean](DomainTheory/DataTypesAsLattices/Continuous/isOpen_basicNhhd.lean)
- [DataTypesAsLattices/Continuous/isOpen_memOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/isOpen_memOpen.lean)
- [DataTypesAsLattices/Continuous/isScottContinuous_determined.lean](DomainTheory/DataTypesAsLattices/Continuous/isScottContinuous_determined.lean)
- [DataTypesAsLattices/Continuous/isScottContinuous_iff_continuous.lean](DomainTheory/DataTypesAsLattices/Continuous/isScottContinuous_iff_continuous.lean)
- [DataTypesAsLattices/Continuous/isScottContinuous_monotone.lean](DomainTheory/DataTypesAsLattices/Continuous/isScottContinuous_monotone.lean)
- [DataTypesAsLattices/Continuous/isScottOpen_basic.lean](DomainTheory/DataTypesAsLattices/Continuous/isScottOpen_basic.lean)
- [DataTypesAsLattices/Continuous/isScottOpen_iff_isOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/isScottOpen_iff_isOpen.lean)
- [DataTypesAsLattices/Continuous/isScottOpen_isUpper.lean](DomainTheory/DataTypesAsLattices/Continuous/isScottOpen_isUpper.lean)
- [DataTypesAsLattices/Continuous/memOpen.lean](DomainTheory/DataTypesAsLattices/Continuous/memOpen.lean)
- [DataTypesAsLattices/Continuous/memOpen_eq_basicNhhd.lean](DomainTheory/DataTypesAsLattices/Continuous/memOpen_eq_basicNhhd.lean)
- [DataTypesAsLattices/Continuous/mem_scottUnion.lean](DomainTheory/DataTypesAsLattices/Continuous/mem_scottUnion.lean)
- [DataTypesAsLattices/Continuous/scottPiece.lean](DomainTheory/DataTypesAsLattices/Continuous/scottPiece.lean)
- [DataTypesAsLattices/Continuous/scottUnion.lean](DomainTheory/DataTypesAsLattices/Continuous/scottUnion.lean)
- [DataTypesAsLattices/Continuous/theorem_1_1.lean](DomainTheory/DataTypesAsLattices/Continuous/theorem_1_1.lean)
- [DataTypesAsLattices/Embedding.lean](DomainTheory/DataTypesAsLattices/Embedding.lean)
- [DataTypesAsLattices/Embedding/Basic.lean](DomainTheory/DataTypesAsLattices/Embedding/Basic.lean)
- [DataTypesAsLattices/Embedding/embed.lean](DomainTheory/DataTypesAsLattices/Embedding/embed.lean)
- [DataTypesAsLattices/Embedding/embed_continuous.lean](DomainTheory/DataTypesAsLattices/Embedding/embed_continuous.lean)
- [DataTypesAsLattices/Embedding/embed_inducing.lean](DomainTheory/DataTypesAsLattices/Embedding/embed_inducing.lean)
- [DataTypesAsLattices/Embedding/embed_injective.lean](DomainTheory/DataTypesAsLattices/Embedding/embed_injective.lean)
- [DataTypesAsLattices/Embedding/extend.lean](DomainTheory/DataTypesAsLattices/Embedding/extend.lean)
- [DataTypesAsLattices/Embedding/isOpen_extend_mem.lean](DomainTheory/DataTypesAsLattices/Embedding/isOpen_extend_mem.lean)
- [DataTypesAsLattices/Embedding/mem_extend.lean](DomainTheory/DataTypesAsLattices/Embedding/mem_extend.lean)
- [DataTypesAsLattices/Embedding/theorem_1_5.lean](DomainTheory/DataTypesAsLattices/Embedding/theorem_1_5.lean)
- [DataTypesAsLattices/Embedding/theorem_1_5_extends.lean](DomainTheory/DataTypesAsLattices/Embedding/theorem_1_5_extends.lean)
- [DataTypesAsLattices/Embedding/theorem_1_6.lean](DomainTheory/DataTypesAsLattices/Embedding/theorem_1_6.lean)
- [DataTypesAsLattices/Embedding/theorem_1_6_injective_continuous.lean](DomainTheory/DataTypesAsLattices/Embedding/theorem_1_6_injective_continuous.lean)
- [DataTypesAsLattices/FixedPoint.lean](DomainTheory/DataTypesAsLattices/FixedPoint.lean)
- [DataTypesAsLattices/FixedPoint/Basic.lean](DomainTheory/DataTypesAsLattices/FixedPoint/Basic.lean)
- [DataTypesAsLattices/FixedPoint/chain_lemma.lean](DomainTheory/DataTypesAsLattices/FixedPoint/chain_lemma.lean)
- [DataTypesAsLattices/FixedPoint/chain_mono.lean](DomainTheory/DataTypesAsLattices/FixedPoint/chain_mono.lean)
- [DataTypesAsLattices/FixedPoint/exists_index_of_finset.lean](DomainTheory/DataTypesAsLattices/FixedPoint/exists_index_of_finset.lean)
- [DataTypesAsLattices/FixedPoint/fix.lean](DomainTheory/DataTypesAsLattices/FixedPoint/fix.lean)
- [DataTypesAsLattices/FixedPoint/iterateBot.lean](DomainTheory/DataTypesAsLattices/FixedPoint/iterateBot.lean)
- [DataTypesAsLattices/FixedPoint/iterateBot_mono.lean](DomainTheory/DataTypesAsLattices/FixedPoint/iterateBot_mono.lean)
- [DataTypesAsLattices/FixedPoint/theorem_1_3.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_3.lean)
- [DataTypesAsLattices/FixedPoint/theorem_1_3_comp.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_3_comp.lean)
- [DataTypesAsLattices/FixedPoint/theorem_1_3_diag.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_3_diag.lean)
- [DataTypesAsLattices/FixedPoint/theorem_1_3_nary.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_3_nary.lean)
- [DataTypesAsLattices/FixedPoint/theorem_1_3_tuple.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_3_tuple.lean)
- [DataTypesAsLattices/FixedPoint/theorem_1_4.lean](DomainTheory/DataTypesAsLattices/FixedPoint/theorem_1_4.lean)
- [DataTypesAsLattices/Graph.lean](DomainTheory/DataTypesAsLattices/Graph.lean)
- [DataTypesAsLattices/Graph/Basic.lean](DomainTheory/DataTypesAsLattices/Graph/Basic.lean)
- [DataTypesAsLattices/Graph/Basic/notation3.lean](DomainTheory/DataTypesAsLattices/Graph/Basic/notation3.lean)
- [DataTypesAsLattices/Graph/IsGraph.lean](DomainTheory/DataTypesAsLattices/Graph/IsGraph.lean)
- [DataTypesAsLattices/Graph/beta.lean](DomainTheory/DataTypesAsLattices/Graph/beta.lean)
- [DataTypesAsLattices/Graph/funOf.lean](DomainTheory/DataTypesAsLattices/Graph/funOf.lean)
- [DataTypesAsLattices/Graph/funOf_isScottContinuous.lean](DomainTheory/DataTypesAsLattices/Graph/funOf_isScottContinuous.lean)
- [DataTypesAsLattices/Graph/funOf_monotone_left.lean](DomainTheory/DataTypesAsLattices/Graph/funOf_monotone_left.lean)
- [DataTypesAsLattices/Graph/funOf_monotone_right.lean](DomainTheory/DataTypesAsLattices/Graph/funOf_monotone_right.lean)
- [DataTypesAsLattices/Graph/graph.lean](DomainTheory/DataTypesAsLattices/Graph/graph.lean)
- [DataTypesAsLattices/Graph/lam.lean](DomainTheory/DataTypesAsLattices/Graph/lam.lean)
- [DataTypesAsLattices/Graph/lam_eq_graph.lean](DomainTheory/DataTypesAsLattices/Graph/lam_eq_graph.lean)
- [DataTypesAsLattices/Graph/mem_funOf.lean](DomainTheory/DataTypesAsLattices/Graph/mem_funOf.lean)
- [DataTypesAsLattices/Graph/mem_graph.lean](DomainTheory/DataTypesAsLattices/Graph/mem_graph.lean)
- [DataTypesAsLattices/Graph/mu_law.lean](DomainTheory/DataTypesAsLattices/Graph/mu_law.lean)
- [DataTypesAsLattices/Graph/theorem_1_2.lean](DomainTheory/DataTypesAsLattices/Graph/theorem_1_2.lean)
- [DataTypesAsLattices/Graph/theorem_1_2_i.lean](DomainTheory/DataTypesAsLattices/Graph/theorem_1_2_i.lean)
- [DataTypesAsLattices/Graph/theorem_1_2_ii.lean](DomainTheory/DataTypesAsLattices/Graph/theorem_1_2_ii.lean)
- [DataTypesAsLattices/Graph/theorem_1_2_iii.lean](DomainTheory/DataTypesAsLattices/Graph/theorem_1_2_iii.lean)
- [DataTypesAsLattices/Pomega.lean](DomainTheory/DataTypesAsLattices/Pomega.lean)
- [DataTypesAsLattices/Pomega/Basic.lean](DomainTheory/DataTypesAsLattices/Pomega/Basic.lean)
- [DataTypesAsLattices/Pomega/BasicInst11.lean](DomainTheory/DataTypesAsLattices/Pomega/BasicInst11.lean)
- [DataTypesAsLattices/Pomega/BasicInst12.lean](DomainTheory/DataTypesAsLattices/Pomega/BasicInst12.lean)
- [DataTypesAsLattices/Pomega/Pomega.lean](DomainTheory/DataTypesAsLattices/Pomega/Pomega.lean)
- [DataTypesAsLattices/Pomega/botElem.lean](DomainTheory/DataTypesAsLattices/Pomega/botElem.lean)
- [DataTypesAsLattices/Pomega/codeFinset.lean](DomainTheory/DataTypesAsLattices/Pomega/codeFinset.lean)
- [DataTypesAsLattices/Pomega/codeList.lean](DomainTheory/DataTypesAsLattices/Pomega/codeList.lean)
- [DataTypesAsLattices/Pomega/e.lean](DomainTheory/DataTypesAsLattices/Pomega/e.lean)
- [DataTypesAsLattices/Pomega/eBelow.lean](DomainTheory/DataTypesAsLattices/Pomega/eBelow.lean)
- [DataTypesAsLattices/Pomega/e_codeFinset.lean](DomainTheory/DataTypesAsLattices/Pomega/e_codeFinset.lean)
- [DataTypesAsLattices/Pomega/e_codeList.lean](DomainTheory/DataTypesAsLattices/Pomega/e_codeList.lean)
- [DataTypesAsLattices/Pomega/e_finite.lean](DomainTheory/DataTypesAsLattices/Pomega/e_finite.lean)
- [DataTypesAsLattices/Pomega/e_or.lean](DomainTheory/DataTypesAsLattices/Pomega/e_or.lean)
- [DataTypesAsLattices/Pomega/e_or_of_subset.lean](DomainTheory/DataTypesAsLattices/Pomega/e_or_of_subset.lean)
- [DataTypesAsLattices/Pomega/e_pow2.lean](DomainTheory/DataTypesAsLattices/Pomega/e_pow2.lean)
- [DataTypesAsLattices/Pomega/e_zero.lean](DomainTheory/DataTypesAsLattices/Pomega/e_zero.lean)
- [DataTypesAsLattices/Pomega/exists_code.lean](DomainTheory/DataTypesAsLattices/Pomega/exists_code.lean)
- [DataTypesAsLattices/Pomega/exists_code_of_finite.lean](DomainTheory/DataTypesAsLattices/Pomega/exists_code_of_finite.lean)
- [DataTypesAsLattices/Pomega/exists_e_mem.lean](DomainTheory/DataTypesAsLattices/Pomega/exists_e_mem.lean)
- [DataTypesAsLattices/Pomega/exists_pair.lean](DomainTheory/DataTypesAsLattices/Pomega/exists_pair.lean)
- [DataTypesAsLattices/Pomega/exists_triangle_bucket.lean](DomainTheory/DataTypesAsLattices/Pomega/exists_triangle_bucket.lean)
- [DataTypesAsLattices/Pomega/le_two_pow.lean](DomainTheory/DataTypesAsLattices/Pomega/le_two_pow.lean)
- [DataTypesAsLattices/Pomega/lt_two_powu27.lean](DomainTheory/DataTypesAsLattices/Pomega/lt_two_powu27.lean)
- [DataTypesAsLattices/Pomega/mem_botElem.lean](DomainTheory/DataTypesAsLattices/Pomega/mem_botElem.lean)
- [DataTypesAsLattices/Pomega/mem_e.lean](DomainTheory/DataTypesAsLattices/Pomega/mem_e.lean)
- [DataTypesAsLattices/Pomega/mem_e_le.lean](DomainTheory/DataTypesAsLattices/Pomega/mem_e_le.lean)
- [DataTypesAsLattices/Pomega/mem_e_lt.lean](DomainTheory/DataTypesAsLattices/Pomega/mem_e_lt.lean)
- [DataTypesAsLattices/Pomega/mem_topElem.lean](DomainTheory/DataTypesAsLattices/Pomega/mem_topElem.lean)
- [DataTypesAsLattices/Pomega/pair.lean](DomainTheory/DataTypesAsLattices/Pomega/pair.lean)
- [DataTypesAsLattices/Pomega/pair_eq_triangle.lean](DomainTheory/DataTypesAsLattices/Pomega/pair_eq_triangle.lean)
- [DataTypesAsLattices/Pomega/pair_inj.lean](DomainTheory/DataTypesAsLattices/Pomega/pair_inj.lean)
- [DataTypesAsLattices/Pomega/pair_le_left.lean](DomainTheory/DataTypesAsLattices/Pomega/pair_le_left.lean)
- [DataTypesAsLattices/Pomega/pair_le_right.lean](DomainTheory/DataTypesAsLattices/Pomega/pair_le_right.lean)
- [DataTypesAsLattices/Pomega/pair_lt_left.lean](DomainTheory/DataTypesAsLattices/Pomega/pair_lt_left.lean)
- [DataTypesAsLattices/Pomega/pair_lt_right.lean](DomainTheory/DataTypesAsLattices/Pomega/pair_lt_right.lean)
- [DataTypesAsLattices/Pomega/pair_unpair.lean](DomainTheory/DataTypesAsLattices/Pomega/pair_unpair.lean)
- [DataTypesAsLattices/Pomega/singleton_eq_e.lean](DomainTheory/DataTypesAsLattices/Pomega/singleton_eq_e.lean)
- [DataTypesAsLattices/Pomega/topElem.lean](DomainTheory/DataTypesAsLattices/Pomega/topElem.lean)
- [DataTypesAsLattices/Pomega/triangle.lean](DomainTheory/DataTypesAsLattices/Pomega/triangle.lean)
- [DataTypesAsLattices/Pomega/triangle_le_of_le.lean](DomainTheory/DataTypesAsLattices/Pomega/triangle_le_of_le.lean)
- [DataTypesAsLattices/Pomega/triangle_le_pair.lean](DomainTheory/DataTypesAsLattices/Pomega/triangle_le_pair.lean)
- [DataTypesAsLattices/Pomega/triangle_lt_of_lt.lean](DomainTheory/DataTypesAsLattices/Pomega/triangle_lt_of_lt.lean)
- [DataTypesAsLattices/Pomega/triangle_succ.lean](DomainTheory/DataTypesAsLattices/Pomega/triangle_succ.lean)
- [DataTypesAsLattices/Pomega/two_pow_le_of_testBit.lean](DomainTheory/DataTypesAsLattices/Pomega/two_pow_le_of_testBit.lean)
- [DataTypesAsLattices/Pomega/union_e_eq.lean](DomainTheory/DataTypesAsLattices/Pomega/union_e_eq.lean)
- [DataTypesAsLattices/Pomega/unpair.lean](DomainTheory/DataTypesAsLattices/Pomega/unpair.lean)
- [DataTypesAsLattices/Pomega/unpair_pair.lean](DomainTheory/DataTypesAsLattices/Pomega/unpair_pair.lean)
