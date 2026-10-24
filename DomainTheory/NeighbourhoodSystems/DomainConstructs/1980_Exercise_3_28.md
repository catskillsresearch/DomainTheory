# Exercise 3.28

## Human-English

**EXERCISE 3.28.** In the function space $(D_0 \to D_1)$ let

$$
\bigcap \{ [X_i, Y_i] \mid i < n \}
$$

be a (non-empty) neighbourhood. In 3.9 the minimal element of this neighbourhood is characterized as a relation $f_0$. Show that as an elementwise mapping it can be defined by the formula

$$
f_0(x) = \bigsqcup \{ \uparrow Y_i \mid x \in [X_i] \} ,
$$

for $x \in |D_0|$. Try to draw a picture of $|D_0|$ with neighbourhoods $[X_i]$ and the corresponding values of the function $f_0$.

<!-- page 55 -->

# LECTURE IV

<u>FIXED POINTS AND RECURSION</u>

Having at this point a large supply of examples of domains (and further constructs of new domains), we now have to consider some other ways of defining functions — other than by explicit compositions of the very basic functions already mentioned. One of the most fruitful techniques is an infinitely iterated composition that is at the back of the idea of recursion. We will use the process over and over again in these lectures, not only to define new functions but also to define new domains. The heart of the matter lies in the so-called "Fixed-point Theorem":

## AI: Human-English to AI-Lean

**[Exercise_3_28.lean](Exercise_3_28.lean)**

@import "Exercise_3_28.lean"
