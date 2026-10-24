# Exercise 2.12

## Human-English

**EXERCISE 2.12.** Suppose $(I, \le)$ is a directed, partially ordered set and $f_i : D_0 \to D_1$ is a family of approximable mappings indexed by $i \in I$, where we assume

$$
i \le j \text{ implies } f_i(x) \subseteq f_j(x)
$$

for all $i, j \in I$ and all $x \in |D_0|$. Prove that there is an approximable mapping $g : D_0 \to D_1$ where

$$
g(x) = \bigcup \{ f_i(x) \mid i \in I \}
$$

for all $x \in |D_0|$.

## AI: Human-English to AI-Lean

**[Exercise_2_12.lean](Exercise_2_12.lean)**

@import "Exercise_2_12.lean"
