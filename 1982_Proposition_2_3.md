# Proposition 2.3

**PROPOSITION 2.3.** *For all $u, v, w, u', v' \in \mathrm{Con}$, we have:*

(i) $\emptyset \vdash \{\Delta\}$;

(ii) $u \vdash v$ implies $u \cup v \in \mathrm{Con}$;

(iii) $u \vdash u$;
(iv) $u \vdash v$ and $v \vdash w$ imply $u \vdash w$;

(v) $u' \supseteq u$, $u \vdash v$, and $v \supseteq v'$ imply $u' \vdash v'$; and

(vi) $u \vdash v$ and $u \vdash v'$ imply $u \vdash v \cup v'$.

Proof. Obvious. ■

*Remark.* It is not worth formulating a formal result at this point, but it should be clear that the properties in 2.3 could have been used as axioms. That is to say, we could have taken $\vdash$ as a binary relation on the set $\mathrm{Con}$, used 2.1 (i)–(ii) and 2.3 (i)–(vi) as axioms. (Actually, 2.3(ii) is redundant.) The old-style entailment relation would then be definable by:

$$
u \vdash X \quad \text{iff} \quad u \vdash \{X\}.
$$

The previous axioms in 2.1 are then easily proved from the new ones. ■

Lean 4

- [InformationSystems/InformationSystems/Proposition23/proposition_2_3_i.lean](DomainTheory/InformationSystems/InformationSystems/Proposition23/proposition_2_3_i.lean)
- [InformationSystems/InformationSystems/Proposition23/proposition_2_3_ii.lean](DomainTheory/InformationSystems/InformationSystems/Proposition23/proposition_2_3_ii.lean)
- [InformationSystems/InformationSystems/Proposition23/proposition_2_3_iii.lean](DomainTheory/InformationSystems/InformationSystems/Proposition23/proposition_2_3_iii.lean)
- [InformationSystems/InformationSystems/Proposition23/proposition_2_3_iv.lean](DomainTheory/InformationSystems/InformationSystems/Proposition23/proposition_2_3_iv.lean)
- [InformationSystems/InformationSystems/Proposition23/proposition_2_3_v.lean](DomainTheory/InformationSystems/InformationSystems/Proposition23/proposition_2_3_v.lean)
- [InformationSystems/InformationSystems/Proposition23/proposition_2_3_vi.lean](DomainTheory/InformationSystems/InformationSystems/Proposition23/proposition_2_3_vi.lean)
