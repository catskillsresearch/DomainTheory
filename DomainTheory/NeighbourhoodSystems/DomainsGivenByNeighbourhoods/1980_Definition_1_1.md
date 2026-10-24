# Definition 1.1

## Human-English

DEFINITION 1.1. A family $\mathcal{D}$ of subsets of a given set $\Delta$ is called a *neighbourhood system* (over $\Delta$) iff it is a non-empty family closed under the intersection of finite consistent sequences of neighbourhoods. That is to say, $\mathcal{D}$ must fulfill these two conditions:

(i) $\Delta \in \mathcal{D}$;

(ii) whenever $X$, $Y$, $Z \in \mathcal{D}$ and $Z \subseteq X \cap Y$, then $X \cap Y \in \mathcal{D}$. $\square$

<!-- page 9 -->

We remark that by convention $\Delta$ corresponds to the intersection of an empty sequence of neighbourhoods; in particular,

$$

## AI: Human-English to AI-Lean

**[NeighborhoodSystem.lean](NeighborhoodSystem.lean)**

@import "NeighborhoodSystem.lean"
