# Proposition 8.10

**PROPOSITION 8.10.** If $a, b : \mathcal{U} \to \mathcal{U}$ are projections, then so are $a + b$, $a \times b$, and $a \to b$. If $a$ and $b$ are finitary, then so are the others; for the fixed-point set of each of them is isomorphic to the corresponding construct applied to the domains determined by $a$ and $b$.
*Proof:* Suppose that $a, b \sqsubseteq I_{\mathcal{U}}$ (= $I$ for short). Then

$$a + b \sqsubseteq I + I = i_+ \circ j_+ \sqsubseteq I.$$

The other cases are similar.

Suppose $a = a \circ a$ and $b = b \circ b$, then, for example,

$$
\begin{aligned}
(a \times b) \circ (a \times b) &= i_\times \circ \langle a \circ \mathrm{proj}_0,\ b \circ \mathrm{proj}_1 \rangle \circ \langle a \circ \mathrm{proj}_0,\ b \circ \mathrm{proj}_1 \rangle \circ j_\times \\
&= i_\times \circ \langle a \circ a \circ \mathrm{proj}_0,\ b \circ b \circ \mathrm{proj}_1 \rangle \circ j_\times \\
&= a \times b.
\end{aligned}
$$

The other cases are similar.

Now in case the fixed-point sets of $a$ and $b$ are domains, they are respectively isomorphic to

$$D_a = \{ X \in \mathcal{U} \mid X \ a \ X \} \quad \text{and}$$
$$D_b = \{ Y \in \mathcal{U} \mid Y \ b \ Y \}.$$

We have to show, for example, that

$$D_a \to D_b \cong D_{a \to b}.$$

Now to simplify matters, remark that the fixed-point set of $a \to b$ on $\mathcal{U}$ is isomorphic to the fixed-point set of $\lambda f.\ b \circ f \circ a$ on $(\mathcal{U} \to \mathcal{U})$. (Hint: use $i_\to$ and $j_\to$ to set up the isomorphism.) So we have to think what it is for an $f : \mathcal{U} \to \mathcal{U}$ to satisfy

$$f = b \circ f \circ a.$$

Notice that we might as well say that $a : \mathcal{U} \to D_a$ and that this map is the other half of an obvious projection pair where

$$i_a : D_a \to \mathcal{U},$$

and $i_a \circ a = a$ and $a \circ i_a = i_a$. So if $g : D_a \to D_b$, let

$$f = i_b \circ g \circ a;$$

then $b \circ f \circ a = f$. Conversely, if $f$ is like this, then let

$$g = b \circ f \circ i_a.$$

Thus, $i_b \circ g \circ a = b \circ f \circ a = f$; so there is an order-preserving isomorphism between the $g : D_a \to D_b$ and the $f = b \circ f \circ a$.
The isomorphism proofs for $+$ and $\times$ are similar. $\square$

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810.lean](../Proposition810.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/Basic.lean](../Proposition810/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/arrowComb_eq.lean](../Proposition810/arrowComb_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/inMapu2080_toElementMap_reaches_left.lean](../Proposition810/inMapu2080_toElementMap_reaches_left.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/inMapu2081_toElementMap_reaches_right.lean](../Proposition810/inMapu2081_toElementMap_reaches_right.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/isProjection_arrowComb.lean](../Proposition810/isProjection_arrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/isProjection_combinators.lean](../Proposition810/isProjection_combinators.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/isProjection_prodComb.lean](../Proposition810/isProjection_prodComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/isProjection_sumComb.lean](../Proposition810/isProjection_sumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/isRetraction_arrowComb.lean](../Proposition810/isRetraction_arrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/isRetraction_lamComb.lean](../Proposition810/isRetraction_lamComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/isRetraction_prodComb.lean](../Proposition810/isRetraction_prodComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/isRetraction_sumComb.lean](../Proposition810/isRetraction_sumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/jPlus_bot_eq_bot.lean](../Proposition810/jPlus_bot_eq_bot.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/lamComb_eq.lean](../Proposition810/lamComb_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/le_idMap_arrowComb.lean](../Proposition810/le_idMap_arrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/le_idMap_lamComb.lean](../Proposition810/le_idMap_lamComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/le_idMap_prodComb.lean](../Proposition810/le_idMap_prodComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/le_idMap_sumComb.lean](../Proposition810/le_idMap_sumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/not_sum_reaches_both.lean](../Proposition810/not_sum_reaches_both.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/prodComb_eq.lean](../Proposition810/prodComb_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/sumComb_eq.lean](../Proposition810/sumComb_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toApproxMap_toElementMap_lamComb.lean](../Proposition810/toApproxMap_toElementMap_lamComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_arrowComb.lean](../Proposition810/toElementMap_arrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_bot_eq_bot_of_comp_eq_idMap.lean](../Proposition810/toElementMap_bot_eq_bot_of_comp_eq_idMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_idem_of_isRetraction.lean](../Proposition810/toElementMap_idem_of_isRetraction.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_le_of_comp_le_idMap.lean](../Proposition810/toElementMap_le_of_comp_le_idMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_le_self_of_le_idMap.lean](../Proposition810/toElementMap_le_self_of_le_idMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_of_comp_eq_idMap.lean](../Proposition810/toElementMap_of_comp_eq_idMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_prodComb.lean](../Proposition810/toElementMap_prodComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_sumComb_mem.lean](../Proposition810/toElementMap_sumComb_mem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_sumComb_of_left.lean](../Proposition810/toElementMap_sumComb_of_left.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_sumComb_of_neither.lean](../Proposition810/toElementMap_sumComb_of_neither.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810/toElementMap_sumComb_of_right.lean](../Proposition810/toElementMap_sumComb_of_right.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b.lean](../Proposition810b.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/IArrowComb.lean](IArrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/IArrowComb_comp_JArrowComb.lean](IArrowComb_comp_JArrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/IProdComb.lean](IProdComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/IProdComb_comp_JProdComb.lean](IProdComb_comp_JProdComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/ISumComb.lean](ISumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/ISumComb_comp_JSumComb.lean](ISumComb_comp_JSumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/JArrowComb.lean](JArrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/JArrowComb_comp_IArrowComb.lean](JArrowComb_comp_IArrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/JProdComb.lean](JProdComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/JProdComb_comp_IProdComb.lean](JProdComb_comp_IProdComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/JSumComb.lean](JSumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/JSumComb_comp_ISumComb.lean](JSumComb_comp_ISumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/arrowComb_elementIso.lean](arrowComb_elementIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/elementIsoOfProjectionPair.lean](elementIsoOfProjectionPair.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/expMap.lean](expMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/expMap_comp.lean](expMap_comp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/expMap_eq.lean](expMap_eq.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/expMap_eq_lamComb.lean](expMap_eq_lamComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/expMap_id.lean](expMap_id.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/finitaryProjection_arrowComb.lean](finitaryProjection_arrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/finitaryProjection_combinators.lean](finitaryProjection_combinators.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/finitaryProjection_prodComb.lean](finitaryProjection_prodComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/finitaryProjection_sumComb.lean](finitaryProjection_sumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/finitary_arrowComb.lean](finitary_arrowComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/finitary_prodComb.lean](finitary_prodComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/finitary_sumComb.lean](finitary_sumComb.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/fixedNbhd_mem_nonempty.lean](fixedNbhd_mem_nonempty.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/inj_comp_proj_eq_self.lean](inj_comp_proj_eq_self.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/isFinitary_of_projectionPair.lean](isFinitary_of_projectionPair.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/prodComb_elementIso.lean](prodComb_elementIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/proposition_8_10.lean](proposition_8_10.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/reaches_neither_iff_eq_bot.lean](reaches_neither_iff_eq_bot.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/sumComb_elementIso.lean](sumComb_elementIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/sumComb_eq_iPlus_sumMap_jPlus.lean](sumComb_eq_iPlus_sumMap_jPlus.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/sumMap_bot.lean](sumMap_bot.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/sumMap_comp.lean](sumMap_comp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/sumMap_id.lean](sumMap_id.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/sumMap_reaches_left.lean](sumMap_reaches_left.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/sumMap_reaches_right.lean](sumMap_reaches_right.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/toApproxMap_toElementMap_expMap.lean](toApproxMap_toElementMap_expMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/toElementMap_bot_eq_bot_of_comp_le_idMap.lean](toElementMap_bot_eq_bot_of_comp_le_idMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/toElementMap_sumMap_inMap₀.lean](toElementMap_sumMap_inMap₀.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/toElementMap_sumMap_inMap₁.lean](toElementMap_sumMap_inMap₁.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/toElementMap_sumMap_of_left.lean](toElementMap_sumMap_of_left.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Proposition810b/toElementMap_sumMap_of_right.lean](toElementMap_sumMap_of_right.lean)
