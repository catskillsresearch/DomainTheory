# Introduction

@import "1976_Continuous_functions.english" {code_block=false}

## Motivation

Give $\{\bot, \top\}$ the weak $T_0$-topology with open sets $\varnothing$, $\{\top\}$, and $\{\bot, \top\}$. That is the Sierpinski space, and the product $\{\bot, \top\}^\omega$ in the product topology is $\mathbf{P}\omega$. The finite sets $e_n$ are the basic open sets of the product. Theorem 1.1 is that observation written out in elementary terms.

On a subspace $X \subseteq \mathbf{P}\omega$ a finite set $e_n$ need not lie in $X$, so continuity of $f : X \to \mathbf{P}\omega$ cannot be written by applying $f$ to $e_n$. Theorem 1.5 is the substitute. Such an $f$ is continuous exactly when it is the restriction of its extension $\bar{f}$, and for $x \in X$ that reads

$$m \in f(x) \quad \text{iff} \quad \exists e_n \subseteq x\;\forall x' \in X\; [e_n \subseteq x' \text{ implies } m \in f(x')].$$

The extension $\bar{f} : \mathbf{P}\omega \to \mathbf{P}\omega$ is continuous for an arbitrary $f$. It extends $f$ precisely when $f$ is continuous.

The fixed-point formula uses the same fact in the form Scott recorded for an increasing sequence: if $x_n \subseteq x_{n+1}$ and $f$ is continuous, then $f$ preserves the union of the $x_n$. Every fixed point lies above every iterate of $\varnothing$, so the union is the least one.

## Historical note

The positive topology came to Scott's attention through Nerode (1959). Continuous functionals had been studied by Kleene, Platek, and others, and Platek (1964) is where monotonicity is stressed. Graphs and application are used in the same way by Plotkin (1972) and by Rogers (1967, p. 147). The fixed-point theorem is Tarski's (1955). The extension theorem is Scott's, in the spirit of point-set topology, and it is the characterization of continuous lattices in Scott (1972). The embedding theorem is the standard one; Čech (1966) is a reference.
