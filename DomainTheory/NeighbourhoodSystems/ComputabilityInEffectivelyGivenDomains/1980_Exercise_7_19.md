# Exercise 7.19

**EXERCISE 7.19.** Prove that $D \mapsto \mathbb{P} D$ is a functor by defining for each $f : D \to E$ a mapping

$$\mathbb{P} f : \mathbb{P} D \to \mathbb{P} E$$

by the formula

$$\bigcup_{i < n} \downarrow X_i \quad \mathbb{P} f \quad \bigcup_{j < m} \downarrow Y_j \quad \text{iff} \quad \forall i < n \exists j < m.\, X_i f Y_j \, .$$

Be sure to check that $\mathbb{P} f$ is approximable and that $\mathbb{P}$ preserves identity maps and composition. If $f$ is computable, is $\mathbb{P} f$? Is there a combinator $\lambda f.\, \mathbb{P} f$? What is

$$\mathbb{P} f(\{x, y\}) = ??$$

**[Exercise_7_19.lean](Exercise_7_19.lean)**

@import "Exercise_7_19.lean"
