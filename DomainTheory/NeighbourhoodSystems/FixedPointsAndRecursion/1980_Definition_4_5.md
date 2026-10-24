# Definition 4.5

## Human-English

**DEFINITION 4.5.** A structured set $\langle \mathbf{N}, 0, {}^+ \rangle$, where $0 \in \mathbf{N}$ and ${}^+ : \mathbf{N} \to \mathbf{N}$ is a unary function, is said to be a *model for Peano's Axioms* if the following conditions are satisfied:

(i) $0 \neq n^+$, for all $n \in \mathbf{N}$;

(ii) $n^+ = m^+$ implies $n = m$, for all $n, m \in \mathbf{N}$;

(iii) whenever $x \subseteq \mathbf{N}$ and $0 \in x$ and $x^+ \subseteq x$, then $x = \mathbf{N}$.

Here $x^+ = \{n^+ \mid n \in x\}$. $\square$

Clause (iii) is recognized as the principle of <u>mathematical induction</u> stated in terms of sets. We usually think of $\mathbf{N}$ as being "God given", and (i)–(iii) as known without question. Suppose God, however, decides to withdraw His set of integers and substitute another. We can ask: "Oh! Why did You take from us our beloved numbers? Why must we now live with these strange new beasts?" God will probably reply "Trust Me!" Perhaps we should in view of the theorem:

## AI: Human-English to AI-Lean

**[Definition_4_5.lean](Definition_4_5.lean)**

@import "Definition_4_5.lean"
