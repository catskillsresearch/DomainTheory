# Proposition 6.12

**PROPOSITION 6.12.** If $D \triangleleft E$, then there exists a projection pair of approximable mappings:

$$
i : D \to E \quad \text{and} \quad j : E \to D
$$

where $j \circ i = I_D$ and $i \circ j \subseteq I_E$, which are determined as element-wise functions by these equations:

$$
i(x) = \{Y \in E \mid \exists X \in x.\, X \subseteq Y\},
$$

and

$$
j(y) = y \cap D,
$$

for all $x \in |D|$ and $y \in |E|$. $\square$

The proof is left for the exercises.

**[Proposition_6_12.lean](Proposition_6_12.lean)**

@import "Proposition_6_12.lean"
