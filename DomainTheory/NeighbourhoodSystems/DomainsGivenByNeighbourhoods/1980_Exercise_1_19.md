# Exercise 1.19

## Human-English

**EXERCISE 1.19.** Define a *positive neighbourhood system* to be a family $\mathcal{D}$ where (ii) of 1.1 is replaced by **(ii')** whenever $X, Y \in \mathcal{D}$, then $X \cap Y \neq \emptyset$ iff $X \cap Y \in \mathcal{D}$. Prove that a positive neighbourhood system is indeed a neighbourhood system in the sense of the earlier definition. Give an example of a neighbourhood system that is *not* positive. (Hint: (suggested by C.A.R. Hoare). Let $\Delta = \mathbf{N} \times \mathbf{N}$, in the plane. Let $\mathcal{D}$ be the family of subsets $X \subseteq \mathbf{N} \times \mathbf{N}$ where all but a finite number of places the *vertical* sections of $X$ are the whole of $\mathbf{N}$ but at the other places the sections are finite and nonempty. Smaller examples are of course possible.)

<!-- page 21 -->

## AI: Human-English to AI-Lean

**[Exercise_1_19.lean](Exercise_1_19.lean)**

@import "Exercise_1_19.lean"
