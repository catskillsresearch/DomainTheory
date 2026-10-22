# Definition 8.9

We have now proved that $\mathcal{U}$ is a nice and big domain that is nicely behaved with respect to computable mappings. It has some very interesting subdomains; to name a few:

$$\mathcal{U} + \mathcal{U}, \quad \mathcal{U} \oplus \mathcal{U}, \quad \mathcal{U} \times \mathcal{U}, \quad \mathcal{U} \otimes \mathcal{U}$$

$$\mathcal{U}_\bot, \quad \mathcal{U}^\infty, \quad \mathcal{U}^\S, \quad \mathbb{P}\mathcal{U}, \quad \mathcal{U} \to \mathcal{U}$$

That all of these are $\trianglelefteq \mathcal{U}$ follows from knowing that they are all effectively presented. What we wish to check next is that they all combine well with respect to projections. To this end the explicit definitions are given for the constructs $+$, $\times$, and $\to$, and the details of the others are left for the exercises.

**DEFINITION 8.9.** Let the computable projection pairs $i_+ : \mathcal{U} + \mathcal{U} \to \mathcal{U}$ and $j_+ : \mathcal{U} \to \mathcal{U} + \mathcal{U}$ be fixed. Similarly choose $i_\times, j_\times$ and $i_\to, j_\to$ for $\mathcal{U} \times \mathcal{U}$ and $\mathcal{U} \to \mathcal{U}$. Define:

$$a + b = \mathrm{cond} \circ \langle \mathrm{which}, i_+ \circ \mathrm{in}_0 \circ a \circ \mathrm{out}_0, i_+ \circ \mathrm{in}_1 \circ b \circ \mathrm{out}_1 \rangle \circ j_+ \ ;$$

$$a \times b = i_\times \circ \langle a \circ \mathrm{proj}_0, b \circ \mathrm{proj}_1 \rangle \circ j_\times \ ;$$

$$a \to b = i_\to \circ (\lambda f.\ b \circ f \circ a) \circ j_\to \ ,$$

for all $a, b : \mathcal{U} \to \mathcal{U}$. $\square$

These interesting(computable!) combinators on elements of $\mathcal{U} \to \mathcal{U}$ have many, many properties. We shall, however, only see what they do to projections.

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/U_mem_nonempty.lean](U_mem_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/funSpaceUU_isEffectivelyGiven.lean](funSpaceUU_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/funSpaceUUPresentation.lean](funSpaceUUPresentation.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iArrow.lean](iArrow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iArrow_comp_jArrow_le.lean](iArrow_comp_jArrow_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iArrow_isComputableMap.lean](iArrow_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iPlus_comp_jPlus_le.lean](iPlus_comp_jPlus_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iPlus_isComputableMap.lean](iPlus_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iTimes_comp_jTimes_le.lean](iTimes_comp_jTimes_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iTimes_isComputableMap.lean](iTimes_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jArrow.lean](jArrow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jArrow_comp_iArrow.lean](jArrow_comp_iArrow.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jArrow_isComputableMap.lean](jArrow_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jPlus_comp_iPlus.lean](jPlus_comp_iPlus.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jPlus_isComputableMap.lean](jPlus_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jTimes_comp_iTimes.lean](jTimes_comp_iTimes.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jTimes_isComputableMap.lean](jTimes_isComputableMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/lamComb.lean](lamComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/arrowComb.lean](arrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/prodUU_isEffectivelyGiven.lean](prodUU_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/prodUUPresentation.lean](prodUUPresentation.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iTimes.lean](iTimes.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jTimes.lean](jTimes.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/prodComb.lean](prodComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/sumUU_isEffectivelyGiven.lean](sumUU_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/sumUUPresentation.lean](sumUUPresentation.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/iPlus.lean](iPlus.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/jPlus.lean](jPlus.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/sumComb.lean](sumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Definition89.lean](../Definition89.lean)
