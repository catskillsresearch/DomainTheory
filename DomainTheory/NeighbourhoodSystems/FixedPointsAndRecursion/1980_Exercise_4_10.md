# Exercise 4.10

## Human-English

**EXERCISE 4.10.** Given a domain $D$ and an element $a \in |D|$, construct a domain $D_a$ where

$$
|D_a| = \{x \in |D| \mid x \sqsubseteq a\}.
$$

Show that if $f : D \to D$ is approximable, then $f$ can be restricted to an approximable map $f' : D_{\mathrm{fix}(f)} \to D_{\mathrm{fix}(f)}$ where $f'(x) = f(x)$ for all $x \in |D_{\mathrm{fix}(f)}|$. How many fixed points does $f'$ have in $|D_{\mathrm{fix}(f)}|$?

<!-- page 68 -->

## AI: Human-English to AI-Lean

**[Exercise_4_10.lean](Exercise_4_10.lean)**

@import "Exercise_4_10.lean"
