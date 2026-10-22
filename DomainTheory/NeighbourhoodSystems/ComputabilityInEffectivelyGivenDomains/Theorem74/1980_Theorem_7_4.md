# Theorem 7.4

The proofs for 7.3 are so trivial they are hardly worth an exercise. Note the immediate and useful consequence: if $f : D \to E$ is computable and $x \in |D|$ is computable, then $f(x) \in |E|$ is also computable. The next result is, however, worth working out even though it is quite easy.

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
Relations in the indices. For this purpose it may be convenient to recall some closure properties of these relations: taking conjunctions, disjunctions, substituting recursive functions, applying an existential quantifier to the front. $\square$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodEnum.lean](prodEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodEnum_apply.lean](prodEnum_apply.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodNbhd_eq_iff.lean](prodNbhd_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodPresentation.lean](prodPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodPresentation_X.lean](prodPresentation_X.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum.lean](sumEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_zero.lean](sumEnum_zero.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_one.lean](sumEnum_one.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_eq_iff.lean](inj₀_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_eq_inj₁_elim.lean](inj₀_eq_inj₁_elim.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_ne_inj₁_of_nonempty.lean](inj₀_ne_inj₁_of_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₀_ne_sumMaster.lean](inj₀_ne_sumMaster.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₁_eq_iff.lean](inj₁_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/inj₁_ne_sumMaster.lean](inj₁_ne_sumMaster.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/recDec_setEq₀.lean](recDec_setEq₀.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/recDec_setEq₁.lean](recDec_setEq₁.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_master.lean](sumEnum_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_mem.lean](sumEnum_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_nonempty.lean](sumEnum_nonempty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_subset_sumMaster.lean](sumEnum_subset_sumMaster.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_inter_sumMaster.lean](sumEnum_inter_sumMaster.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumMaster_inter_sumEnum.lean](sumMaster_inter_sumEnum.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/tag_trichotomy.lean](tag_trichotomy.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumEnum_eq_iff.lean](sumEnum_eq_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/eqSEdec.lean](eqSEdec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/sumPresentation.lean](sumPresentation.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/paired_isComputable.lean](paired_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prod_isEffectivelyGiven.lean](prod_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/proju2080_isComputable.lean](proju2080_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/proju2081_isComputable.lean](proju2081_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74/prodMap_isComputable.lean](prodMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem74.lean](../Theorem74.lean)
