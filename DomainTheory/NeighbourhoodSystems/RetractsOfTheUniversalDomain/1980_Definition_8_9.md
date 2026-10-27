# Definition 8.9

**DEFINITION 8.9.** Let the computable projection pairs $i_+ : \mathcal{U} + \mathcal{U} \to \mathcal{U}$ and $j_+ : \mathcal{U} \to \mathcal{U} + \mathcal{U}$ be fixed. Similarly choose $i_\times, j_\times$ and $i_\to, j_\to$ for $\mathcal{U} \times \mathcal{U}$ and $\mathcal{U} \to \mathcal{U}$. Define:

$$a + b = \mathrm{cond} \circ \langle \mathrm{which}, i_+ \circ \mathrm{in}_0 \circ a \circ \mathrm{out}_0, i_+ \circ \mathrm{in}_1 \circ b \circ \mathrm{out}_1 \rangle \circ j_+ \ ;$$

$$a \times b = i_\times \circ \langle a \circ \mathrm{proj}_0, b \circ \mathrm{proj}_1 \rangle \circ j_\times \ ;$$

$$a \to b = i_\to \circ (\lambda f.\ b \circ f \circ a) \circ j_\to \ ,$$

for all $a, b : \mathcal{U} \to \mathcal{U}$. $\square$

These interesting(computable!) combinators on elements of $\mathcal{U} \to \mathcal{U}$ have many, many properties. We shall, however, only see what they do to projections.

**[Definition_8_9.lean](Definition_8_9.lean)** — embeddings and `prodComb` / `arrowComb`

@import "Definition_8_9.lean"

**[sumComb.lean](sumComb.lean)** — `sumComb` and Pref-folded companions

@import "sumComb.lean"
