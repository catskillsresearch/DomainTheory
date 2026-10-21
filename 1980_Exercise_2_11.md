# Exercise 2.11

**EXERCISE 2.11.** Let $(I, \le)$ be a non-empty abstract partially ordered set; suppose it is <u>directed</u> in the sense that whenever $i, j \in I$, then $i \le k$ and $j \le k$ for some $k \in I$. Suppose that $a : I \to |D|$ is such that

$$
i \le j \text{ implies } a_i \subseteq a_j
$$

for all $i, j \in I$. Prove that

$$
\bigcup \{ a_i \mid i \in I \}
$$

is always a filter in $|D|$. (Note the ways this lemma could be used in the proof of 2.7; but be careful in defining the partially ordered set and do not confuse $\subseteq$ and $\supseteq$.) In words we could say that the domain of filters is <u>closed under directed unions</u>. Prove also that if $f : D \to D'$ is an approximable mapping, then for any directed union

$$
f(\bigcup \{ a_i \mid i \in I \}) = \bigcup \{ f(a_i) \mid i \in I \};
$$

that is, <u>approximable mappings always preserve directed unions</u>. If an elementwise function preserves directed unions, must it come from an approximable mapping? (Hint: Invoke 2.9.)
