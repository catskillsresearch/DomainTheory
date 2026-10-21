# Theorem 6.6

**THEOREM 6.6 (The $\mathfrak{B}$ theorem).** *The sets that are Boolean combinations of open sets are exactly the sets of the form:*

$$\{x \mid f(x) \in \mathcal{E}\},$$

*where $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is continuous and $\mathcal{E}$ is a finite set of finite elements of $\mathbf{P}\omega$.*

To see that every $\mathfrak{B}$ set has this form, suppose that

$$V = W_0 \cup W_1 \cup \cdots \cup W_{n-1},$$

where each $W_i \in \mathfrak{F} \dot{\cap} \mathfrak{G}$. We can write:

$$W_i = \{x \mid f_i(x) = 0\},$$

where $f_i : \mathbf{P}\omega \to \{\bot, 0, \top\}$ is continuous. Then define:

$$g(x) = \{2i + j \mid j \in f_i(x) \cap \{0, 1\}, i < n\},$$

and note that $g$ is continuous. Let

$$\mathcal{E} = \{y \subseteq \{m \mid m < 2n\} \mid \exists i < n . 2i \in y, 2i+1 \notin y\};$$

we have:

$$V = \{x \mid g(x) \in \mathcal{E}\}$$

as desired.
