/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import DomainTheory.DataTypesAsLattices.Embedding

/-!
# Scott 1976, §2 — LAMBDA, combinators, and the first recursion theorem

Table 2, equations (2.1)–(2.28), Theorems 2.1–2.5.
-/

namespace DomainTheory.DataTypesAsLattices

/-- Scott's integer convention: `n = {n}` as an element of `Pω`. -/
def ofNat (n : ℕ) : Pomega := {n}

@[simp] theorem mem_ofNat {n k : ℕ} : k ∈ ofNat n ↔ k = n := by simp [ofNat]

/-- **Scott 1976, (2.2).** Minimal (distributive) extension `p̂(x) = ⋃ {p(n) | n ∈ x}`. -/
def minExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  ⋃ n ∈ x, p n

/-- **Scott 1976, (2.1).** Maximal extension, written without a decidability side condition. -/
def maxExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  {k | (x = ∅ ∧ ∀ n, k ∈ p n) ∨
    (∃ n, x = ofNat n ∧ k ∈ p n) ∨
    (x ≠ ∅ ∧ ∀ n, x ≠ ofNat n)}

/-- **Scott 1976, Table 2.** Successor `x + 1 = {n + 1 | n ∈ x}`. -/
def succSet (x : Pomega) : Pomega :=
  {k | ∃ n ∈ x, k = n + 1}

/-- **Scott 1976, Table 2.** Predecessor `x − 1 = {n | n + 1 ∈ x}`. -/
def predSet (x : Pomega) : Pomega :=
  {k | k + 1 ∈ x}

/-- **Scott 1976, Table 2.** McCarthy conditional. -/
def condSet (z x y : Pomega) : Pomega :=
  {n | n ∈ x ∧ 0 ∈ z} ∪ {m | m ∈ y ∧ ∃ k, k + 1 ∈ z}

/-- **Scott 1976, (4.4).** Doubly strict conditional
`z ⊒ x, y = z ⊃ (z ⊃ x, ⊤), (z ⊃ ⊤, y)`. -/
def dcondSet (z x y : Pomega) : Pomega :=
  condSet z (condSet z x topElem) (condSet z topElem y)

/-- **Scott 1976, Table 2.** Syntax of LAMBDA. -/
inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | pred : Term → Term
  | cond : Term → Term → Term → Term
  | app : Term → Term → Term
  | lam : ℕ → Term → Term

def envSet (ρ : ℕ → Pomega) (i : ℕ) (v : Pomega) : ℕ → Pomega :=
  Function.update ρ i v

/-- **Scott 1976, Table 2.** Semantics of a LAMBDA term. -/
def interp : Term → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => ofNat 0
  | .succ t, ρ => succSet (interp t ρ)
  | .pred t, ρ => predSet (interp t ρ)
  | .cond z x y, ρ => condSet (interp z ρ) (interp x ρ) (interp y ρ)
  | .app u x, ρ => funOf (interp u ρ) (interp x ρ)
  | .lam i body, ρ => graph (fun v => interp body (envSet ρ i v))

/-- `i` occurs anywhere in `t` (free or bound). Freshness for (α). -/
def Occurs (i : ℕ) : Term → Prop
  | .var j => j = i
  | .zero => False
  | .succ t => Occurs i t
  | .pred t => Occurs i t
  | .cond z x y => Occurs i z ∨ Occurs i x ∨ Occurs i y
  | .app u x => Occurs i u ∨ Occurs i x
  | .lam k body => k = i ∨ Occurs i body

/-- Rename free `i` to a completely fresh `j`. -/
def rename (i j : ℕ) : Term → Term
  | .var k => if k = i then .var j else .var k
  | .zero => .zero
  | .succ t => .succ (rename i j t)
  | .pred t => .pred (rename i j t)
  | .cond z x y => .cond (rename i j z) (rename i j x) (rename i j y)
  | .app u x => .app (rename i j u) (rename i j x)
  | .lam k body => if k = i then .lam k body else .lam k (rename i j body)

def curry2 (f : Pomega → Pomega → Pomega)
    (_hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (_hfy : ∀ x, IsScottContinuous (fun y => f x y)) : Pomega :=
  graph (fun x => graph (fun y => f x y))

def curry3 (f : Pomega → Pomega → Pomega → Pomega)
    (_hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (_hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (_hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => f x y z)))

/-- Continuity of an n-ary map, taken one argument at a time from the left. -/
def IsScottContinuousFin : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Prop
  | 0, _ => True
  | n + 1, f =>
      (∀ xs : Fin n → Pomega, IsScottContinuous (fun x => f (Fin.cons x xs))) ∧
      (∀ x : Pomega, IsScottContinuousFin (fun xs : Fin n → Pomega => f (Fin.cons x xs)))

/-- Nested-graph representative of an n-ary continuous map. -/
def curryFin : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Pomega
  | 0, f => f Fin.elim0
  | _n + 1, f => graph (fun x => curryFin (fun xs => f (Fin.cons x xs)))

/-- Iterated application of a nested-graph representative. -/
def nestApplyFin (u : Pomega) : ∀ {n : ℕ}, (Fin n → Pomega) → Pomega
  | 0, _ => u
  | _n + 1, xs => nestApplyFin (funOf u (xs 0)) (Fin.tail xs)

def zeroC : Pomega := ofNat 0
def sucC : Pomega := graph succSet
def predC : Pomega := graph predSet
def condC : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => condSet z x y)))
def Kcomb : Pomega := graph (fun x => graph (fun _ => x))
def Scomb : Pomega :=
  graph (fun u => graph (fun v => graph (fun x => funOf (funOf u x) (funOf v x))))

/-- Combinatory closure of the six constants of Theorem 2.4. -/
inductive IsCombinatory : Pomega → Prop
  | zero : IsCombinatory zeroC
  | suc : IsCombinatory sucC
  | pred : IsCombinatory predC
  | cond : IsCombinatory condC
  | K : IsCombinatory Kcomb
  | S : IsCombinatory Scomb
  | app {u v} : IsCombinatory u → IsCombinatory v → IsCombinatory (funOf u v)

/-- **Scott 1976, (2.8).** `ω(u) = λ x. u(x(x))`. -/
def omegaComb (u : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf x x))

/-- **Scott 1976, (2.8).** `Y = λ u. ω(u)(ω(u))`. -/
def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))

/-- **Scott 1976, (2.19)–(2.21).** Finite sequences as distributive functions. -/
def seq0 : Pomega := botElem

def seq1 (x : Pomega) : Pomega :=
  graph (fun z => condSet z x botElem)

def seq2 (x y : Pomega) : Pomega :=
  graph (fun z => condSet z x (condSet (predSet z) y botElem))

/-- **Scott 1976, (2.3).** Relational composition. -/
def relComp (x y : Pomega) : Pomega :=
  {p | ∃ n m l, p = pair n l ∧ pair n m ∈ x ∧ pair m l ∈ y}

/-- **Scott 1976, (2.4).** Set-sum. -/
def setSum (x y : Pomega) : Pomega :=
  {k | ∃ n m, n ∈ x ∧ m ∈ y ∧ k = n + m}

/-- **Scott 1976, (2.16).** `⊤ = Y(λx. 0 ∪ (x + 1))`. -/
def topRec (x : Pomega) : Pomega := ofNat 0 ∪ succSet x

/-- Combinatory expressions generated from the six constants and variables. -/
inductive Comb where
  | var : ℕ → Comb
  | zero | suc | pred | cond | K | S
  | app : Comb → Comb → Comb

def ofComb : Comb → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => zeroC
  | .suc, _ => sucC
  | .pred, _ => predC
  | .cond, _ => condC
  | .K, _ => Kcomb
  | .S, _ => Scomb
  | .app u v, ρ => funOf (ofComb u ρ) (ofComb v ρ)

def abs (i : ℕ) : Comb → Comb
  | .var j => if j = i then .app (.app .S .K) .K else .app .K (.var j)
  | .zero => .app .K .zero
  | .suc => .app .K .suc
  | .pred => .app .K .pred
  | .cond => .app .K .cond
  | .K => .app .K .K
  | .S => .app .K .S
  | .app u v => .app (.app .S (abs i u)) (abs i v)

def erase : Term → Comb
  | .var i => .var i
  | .zero => .zero
  | .succ t => .app .suc (erase t)
  | .pred t => .app .pred (erase t)
  | .cond z x y => .app (.app (.app .cond (erase x)) (erase y)) (erase z)
  | .app u x => .app (erase u) (erase x)
  | .lam i body => abs i (erase body)

/-- **Scott 1976, §2.** The subspace `FUN` of graphs. -/
def FUN : Set Pomega := {u | u = graph (funOf u)}

/-- **Scott 1976, (2.22).** Longer sequences by cons. -/
def seqCons (x xs : Pomega) : Pomega :=
  graph (fun z => condSet z x (funOf xs (predSet z)))

/-- Least operator solving the (2.17) recursion. -/
def interStep (f : Pomega) : Pomega :=
  graph (fun x => graph (fun y =>
    condSet x (condSet y (ofNat 0) botElem)
      (succSet (funOf (funOf f (predSet x)) (predSet y)))))

def interC : Pomega := fix interStep

/-- **Scott 1976, (2.24)–(2.25).** Revaluation as a distributive sequence. -/
def seqFun (u x : Pomega) : Pomega :=
  ⋃ i ∈ x, funOf u (ofNat i)

def dollarC : Pomega :=
  graph (fun u => graph (fun x => seqFun u x))

/-- Shift of a sequence: `(λt. u_{t+1})`. -/
def seqShift (u : Pomega) : Pomega :=
  graph (fun z => seqFun u (succSet z))

/-- **Scott 1976, (2.24).** The step of `$ = Y(λs λu λz. z ⊃ u₀, s(λt. u_{t+1})(z−1))`. -/
def dollarStepBody (s u z : Pomega) : Pomega :=
  condSet z (funOf u (ofNat 0))
    (funOf (funOf s (seqShift u)) (predSet z))

def dollarStep (s : Pomega) : Pomega :=
  graph (fun u => graph (fun z => dollarStepBody s u z))

/-- Finite stage of the `$` iteration: `⋃ { uᵢ | i ∈ x, i < n }`. -/
def seqFunLt (u x : Pomega) (n : ℕ) : Pomega :=
  ⋃ i ∈ x, ⋃ _ : i < n, funOf u (ofNat i)

/-- **Scott 1976, (2.26).** `λn∈ω. τ` is `$` applied to a graph. -/
def lamOmega (τ : ℕ → Pomega) : Pomega :=
  funOf dollarC (graph (fun z => ⋃ n ∈ z, τ n))

/-- **Scott 1976, (2.27).** Primitive recursion as a distributive function. -/
def primRecVal (a f : Pomega) : ℕ → Pomega
  | 0 => a
  | n + 1 => funOf (funOf f (ofNat n)) (primRecVal a f n)

def primRecHat (a f x : Pomega) : Pomega :=
  ⋃ n ∈ x, primRecVal a f n

def primRecStep (a f u : Pomega) : Pomega :=
  graph (fun n => condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))))

def Ymap (g : Pomega → Pomega → Pomega) : Pomega :=
  graph (fun x => fix (g x))

def Fofg (g : Pomega → Pomega → Pomega) (f : Pomega) : Pomega :=
  graph (fun x => g x (funOf f x))

/-- Closed term for `Y`. -/
def Yterm : Term :=
  .lam 0 (.app
    (.lam 1 (.app (.var 0) (.app (.var 1) (.var 1))))
    (.lam 1 (.app (.var 0) (.app (.var 1) (.var 1)))))

/-- Term-level shift `λt. u(t+1)`, which agrees with `seqShift` on numerals. -/
def termShift (u : Pomega) : Pomega :=
  graph (fun t => funOf u (succSet t))

/-- Paper combinator for `$`: `λs λu λz. z ⊃ u(0), s(λt. u(t+1))(z−1)`. -/
def dollarStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 2)
      (.app (.var 1) .zero)
      (.app (.app (.var 0) (.lam 3 (.app (.var 1) (.succ (.var 3)))))
        (.pred (.var 2))))))

def termDollarStepBody (s u z : Pomega) : Pomega :=
  condSet z (funOf u (ofNat 0))
    (funOf (funOf s (termShift u)) (predSet z))

def termDollarStep (s : Pomega) : Pomega :=
  graph (fun u => graph (fun z => termDollarStepBody s u z))

/-- Combinatory primitive-recursion step `λa λf λu λn. n ⊃ a, f(n−1)(u(n−1))`. -/
def primRecStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2 (.lam 3
    (.cond (.var 3) (.var 0)
      (.app (.app (.var 1) (.pred (.var 3)))
        (.app (.var 2) (.pred (.var 3))))))))
end DomainTheory.DataTypesAsLattices
