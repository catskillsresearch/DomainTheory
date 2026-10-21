# Theorem 4.2

**THEOREM 4.2 (The partial ordering theorem).** The retracts are partially ordered by $\sqsubseteq$.

There do not seem to be any lattice properties of $\sqsubseteq$ of a general nature. Note, however, that if retracts commute, $a \circ b = b \circ a$, then $a \circ b$ is the greatest lower bound under $\sqsubseteq$ of $a$ and $b$. Also if we have a sequence where both $a_n \sqsubseteq a_{n+1}$ and $a_n \subseteq a_{n+1}$ for all $n \in \omega$, then $\bigcup\{a_n \mid n \in \omega\}$ is the upper bound for the $a_n$ under $\sqsubseteq$, as can easily be argued from the definition by continuity of $\circ$.

Certainly there is no “least” retract under $\sqsubseteq$. One has $\bot = \bot \circ a$ (recall: $\bot = \lambda x.\,\bot$), but not $a \circ \bot = \bot$. This last equation means more simply that $a(\bot) = \bot$; that is, $a$ is *strict*. For retracts strictness is thus equivalent to $\bot \sqsubseteq a$, so we can say that there is a least strict retract. The combinator $\mathbf{I} = \lambda u.\, u$ clearly represents the largest retract (the *whole space*), and it is strict also. In a certain sense strictness can be assumed without loss of generality. For if $a$ is not strict, let

$$b = \lambda x.\, \{n \mid a(x) \neq a(\bot)\}.$$

This function takes values in $\{\bot, \top\}$ and is continuous because $\{x \in \mathbf{P}\omega \mid a(x) \neq a(\bot)\}$ is *open*. Next define:

$$a^* = \lambda u.\, a(u) \cap b(u).$$

This is a strict retract whose range is homeomorphic (and lattice isomorphic) to that of $a$. Note, however, that the mapping from $a$ to $a^*$ is not continuous (or even monotonic).

To have a more uniform notation for retracts we shall often write **nil**, **id**, and **seq** for the combinators $\bot$, $\mathbf{I}$, $\mathbf{\$}$. Two further retracts of interest are

$$(4.6) \quad \mathbf{open} = \lambda u.\, \{m \mid \exists e_n \subseteq e_m.\, n \in u\};$$

$$(4.7) \quad \mathbf{int} = \lambda u.\, u \supset 0,\, \mathbf{int}(u - 1) \supset u,\, u.$$

The range of **open** is lattice isomorphic to the lattice of open subsets of $\mathbf{P}\omega$; definition (4.6) is not a LAMBDA-definition of the retract, but such can be given.

In (4.7) we intend **int** to be the least fixed point of the equation. By induction on the least element of $u$ (if any) one proves that:

$$\mathbf{int}(u) = \begin{cases} \bot & \text{if } u = \bot; \\ u & \text{if } u \in \omega; \\ \top & \text{otherwise.} \end{cases}$$

This retract wipes out the distinctions between multiple values, moving all above the singletons up to $\top$; its range thus has a very simple structure. The retract **int** clearly generalizes **bool**. The range of **fun** is homeomorphic to the space of all continuous functions from $\mathbf{P}\omega$ into $\mathbf{P}\omega$; the range of **pair**, to the space of all ordered pairs; the range of **seq**, to the space of all infinite sequences. A combination like $\lambda u.\, \mathbf{int} \circ \mathbf{seq}(u)$ is a retract whose range is homeomorphic to the space of infinite sequences of elements from the range of **int**.

We now wish to introduce some operators that provide systematic ways of forming new combinations of retracts. There are three principal ones:

$$(4.8) \quad a \circ\to b = \lambda u.\, b \circ u \circ a;$$

$$(4.9) \quad a \otimes b = \lambda u.\, \langle a(u_0), b(u_1) \rangle;$$

$$(4.10) \quad a \oplus b = \lambda u.\, u_0 \supset \langle 0, a(u_1) \rangle,\, \langle 1, b(u_1) \rangle.$$

These equations clearly generalize (4.1)–(4.3). Before we explain our operators, note these three equations which hold for arbitrary $a, b, a', b'$:

$$(4.11) \quad (a \circ\to b) \circ (a' \circ\to b') = (a' \circ a) \circ\to (b \circ b');$$

$$(4.12) \quad (a \otimes b) \circ (a' \otimes b') = (a \circ a') \otimes (b \circ b');$$

$$(4.13) \quad (a \oplus b) \circ (a' \oplus b') = (a \circ a') \oplus (b \circ b').$$

The reversal of order $(a' \circ a)$ on the right-hand side of (4.11) should be remarked.

These equations will be used not only for properties of types (ranges of retracts) but also for the mappings between the types.

**Lean 4**

- [DataTypesAsLattices/Retracts/theorem_4_2.lean](theorem_4_2.lean)
