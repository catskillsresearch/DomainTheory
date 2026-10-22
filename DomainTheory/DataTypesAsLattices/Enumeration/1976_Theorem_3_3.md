# Theorem 3.3

**THEOREM 3.3 (The second recursion theorem).** Take a LAMBDA-definable element $v$ such that:

*(i)* $\mathbf{val}(v(n)) = \lambda m \in \omega.\, \mathbf{val}(n)(\mathbf{apply}(m)(\mathbf{num}(m)))$,

and then define a combinator by:

*(ii)* $\mathbf{rec} = \lambda n \in \omega.\, \mathbf{apply}(v(n))(\mathbf{num}(v(n)))$.

Then we have a primitive recursive function with this fixed-point property:

*(iii)* $\mathbf{val}(\mathbf{rec}(n)) = \mathbf{val}(n)(\mathbf{rec}(n))$.

Note that if $u$ is LAMBDA-definable, then we find first an $n$ such that $\mathbf{val}(n) = u$. Next we calculate $k = \mathbf{rec}(n)$. This effectively gives us an integer such that $\mathbf{val}(k) = u(k)$. Gödel numbers represent expressions (combinations in $\mathbf{G}$), and $\mathbf{val}$ maps the numbers to the values denoted by the expressions in the model. The $k$ just found thus represents an expression whose value is defined in terms of its own Gödel number. In recursion theory there are many applications of this result. Another familiar argument shows:

**Lean 4**

- [DataTypesAsLattices/Enumeration/theorem_3_3_from_v.lean](theorem_3_3_from_v.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3_i.lean](theorem_3_3_i.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3_ii.lean](theorem_3_3_ii.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3.lean](theorem_3_3.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_3_val.lean](theorem_3_3_val.lean)
