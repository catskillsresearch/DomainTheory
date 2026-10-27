# Exercise 3.19

**EXERCISE 3.19.** Suppose we are given systems and approximable mappings

$$
f : \mathcal{D}_0 \to \mathcal{D}'_0 \quad \text{and} \quad g : \mathcal{D}_1 \to \mathcal{D}'_1.
$$

Prove there are approximable mappings

$$
f \times g : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}'_0 \times \mathcal{D}'_1 \quad \text{and} \quad f + g : \mathcal{D}_0 + \mathcal{D}_1 \to \mathcal{D}'_0 + \mathcal{D}'_1
$$

such that

(i) $(f \times g)(x, y) = \langle f(x), g(y) \rangle$ for all $x \in |\mathcal{D}_0|$ and $y \in |\mathcal{D}_1|$, and rewrite this as:

(ii) $f \times g = \langle f \circ p_0, g \circ p_1 \rangle$.

In addition prove that

(iii) $out_0 \circ (f + g) \circ in_0 = f$, and

(iv) $out_1 \circ (f + g) \circ in_1 = g$.

Do equations (iii) and (iv) uniquely determine $f + g$?

<!-- page 52 -->

**[Exercise_3_19.lean](Exercise_3_19.lean)**

@import "Exercise_3_19.lean"

**[../RetractsOfTheUniversalDomain/sumMap.lean](../RetractsOfTheUniversalDomain/sumMap.lean)** — Pref-folded `sumMap` companions

@import "../RetractsOfTheUniversalDomain/sumMap.lean"
