# Exercise 4.11

**EXERCISE 4.11.** (Suggested by G. Plotkin). We can regard $\mathrm{fix}$ as assigning a fixed-point operator to each domain $D$. Show that $\mathrm{fix}$ is uniquely determined by the following general conditions on an assignment $D \rightsquigarrow F_D$:

(i) $F_D : (D \to D) \to D$;

(ii) $F_D(f) = f(F_D(f))$ for all $f : D \to D$;

(iii) whenever $f_0 : D_0 \to D_0$ and $f_1 : D_1 \to D_1$ are given and $h : D_0 \to D_1$ is such that $h(\perp) = \perp$ and $h \circ f_0 = f_1 \circ h$, then $h(F_{D_0}(f_0)) = F_{D_1}(f_1)$.

(Hint: Apply 4.7 to prove $\mathrm{fix}$ satisfies (iii). In the other direction use 4.10.)

**[Exercise_4_11.lean](Exercise_4_11.lean)**

@import "Exercise_4_11.lean"
