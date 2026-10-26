# Definition 2.1

**DEFINITION 2.1.** An *approximable mapping* $f : D_0 \to D_1$ between domains is a binary relation $f \subseteq D_0 \times D_1$ between neighbourhoods such that

(i) $\Delta_0 f \Delta_1$ ;

(ii) $X f Y$ and $X f Y'$ always imply $X f (Y \cap Y')$ ;

(iii) $X f Y$, $X' \subseteq X$, and $Y \subseteq Y'$ always imply $X' f Y'$. $\square$

Condition (i) we have already discussed; in a sense it means “ask me no questions and I shall tell you no lies.” In other words “zero input can expect at least zero output.” The other conditions are compatible with having

$$
f = \{ \langle X, \Delta_1 \rangle \mid X \in D_0 \};
$$

that is, $f$ might be the least informative relation and nothing more. But if it is more, then (ii) is, as we explained, a consistency condition. To explain monotonicity in (iii), suppose a mapping relationship is already known, $X f Y$, say. If we *improve* the accuracy of $X$ to $X' \subseteq X$ and if we *degrade* the accuracy of $Y$ to $Y' \supseteq Y$, then we can still assert $X' f Y'$ since this relationship is *less informative* than the former relationship, which was already known. Thus, we see that conditions (i)–(iii) are all reasonably argued as necessary.

One indication that the conditions of 2.1 are sufficient for a definition is that they are exactly what we need to show that $f$ as a neighbourhood relation determines an equivalent elementwise mapping from $|D_0|$ into $|D_1|$. (Owing to the equivalence, we use the same symbol $f$ for both.)

**[Definition_2_1.lean](Definition_2_1.lean)**

@import "Definition_2_1.lean"
