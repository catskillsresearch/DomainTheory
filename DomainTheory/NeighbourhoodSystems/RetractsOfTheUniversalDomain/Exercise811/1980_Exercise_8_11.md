# Exercise 8.11

Well, this was a lot of work, but the pay-off is rather handsome. What we have done is transpose all the

$$D_a \triangleleft U$$

over to finitary projections $a : U \to U$. This transposition is an isomorphism, because

$$D_a \triangleleft D_b \text{ iff } a \sqsubseteq b.$$

Moreover, by the method of 8.9 and 8.10, all our favourite constructs have been made into *combinators*, that is, approximable — even computable — maps on the domain of finitary projections. *ALL APPROXIMABLE (COMPUTABLE) MAPS HAVE (COMPUTABLE) FIXED POINTS.* And there you are! The standard fixed-point method is available to obtain computable (i.e. effectively given) solutions to *all* domain equations (even sets of equations) where the constructs can be reworked in *this* way to be defined on projections. Examples are suggested in the exercises.

Another pay-off concerns the $\lambda$-calculus itself. Inasmuch as

$$U + U, \quad U \times U, \quad U \to U \triangleleft U,$$

we might just as well forget the outside world and regard all these useful domains as being part of $U$. For example, on the left we have the new notation and on the right the old notation:

$$
\begin{aligned}
\mathrm{which}(z) &= \mathrm{which}(j_+(z)) ; \\
\mathrm{in}_i(x) &= i_+(\mathrm{in}_i(x)), \quad i = 0, 1 ; \\
\mathrm{out}_i(x) &= \mathrm{out}_i(j_+(x)), \quad i = 0, 1 ; \\
\langle x, y \rangle &= i_\times(\langle x, y \rangle) ; \\
\mathrm{proj}_i(z) &= \mathrm{proj}_i(j_\times(z)), \quad i = 0, 1 ; \\
u(x) &= j_\to(u)(x) ; \\
\lambda x.\,\tau &\cong i_\to(\lambda x.\,\tau) .
\end{aligned}
$$

And, there is no reason to stop here. The system

$$T \cong \{\{0, 1/2\}, \{1/2, 1\}, \{0, 1\}\} \triangleleft U,$$

so we might as well think of
$$\text{true, false} \in |U|$$

and think of $\mathrm{cond} : U \times U \times U \to U$. No! that is wrong: under the new regime *EVERYTHING IS AN ELEMENT OF U*. With the new meaning of $\lambda$, all functions, all pairs, all combinators, all constructs become elements of $U$.

It takes a little time to get used to "universal conscription" with all elements doing (at least) double duty in the same domain, but there are many advantages, both notational and conceptual.

**EXERCISES**

**EXERCISE 8.11.** Let $\mathbb{Q}$ be the set of rational numbers and define a neighbourhood system by the equation

$$R = \{[0, r) \mid r \in \mathbb{Q} \text{ and } 0 < r \le 1\}.$$

Show that the following defines an approximable map $a : R \to R$:

$$[0, r) \ a \ [0, s) \quad \text{iff} \quad r < s \text{ or } r = s = 1.$$

Show in addition that $a$ is a projection where the fixed-point set of $a$ is in a one-one correspondence with the *real* numbers between 0 and 1 inclusive. (Hint: Recall Dedekind cuts and show $\subseteq$ matches $\le$.) Conclude that $a$ is *NOT* finitary. (Hint: Aside from $\bot$ there are no finite elements for $\{x \mid x = a(x)\}$.)

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/Ico0_inj.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/Ico0_inj.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/Ico0_inter.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/Ico0_inter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/Ico0_le_of_subset.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/Ico0_le_of_subset.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/R.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/R.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/R_master.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/R_master.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/R_mem_Ico0.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/R_mem_Ico0.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/R_mem_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/R_mem_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/a.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/a.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/aRel.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/aRel.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/aRel_combine.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/aRel_combine.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/aRel_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/aRel_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/aRel_le.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/aRel_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/a_rel.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/a_rel.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt_cutPoint.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt_cutPoint.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt_injective.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt_injective.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt_le_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt_le_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt_mem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutElt_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutPoint.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutPoint.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutPoint_le_one.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutPoint_le_one.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutPoint_nonneg.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutPoint_nonneg.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutS.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutS.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutS_bddBelow.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutS_bddBelow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutS_nonempty.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutS_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_le1.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_le1.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_mono.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_mono.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_one.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_one.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_pos.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_pos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_up.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/cutU_up.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/ext_U.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/ext_U.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/fixOrderIso.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/fixOrderIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/isProjection_a.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/isProjection_a.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/isRetraction_a.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/isRetraction_a.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/le_iff_U.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/le_iff_U.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/mkElement.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/mkElement.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/mkElement_mem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/mkElement_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/not_isCompactElt_pos.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/not_isCompactElt_pos.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/not_isFinitary_a.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/not_isFinitary_a.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/toElementMap_cutElt.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Exercise811/toElementMap_cutElt.lean)
