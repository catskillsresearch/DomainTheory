/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

/-!
# Scott 1976, §2 — computability and the definability theorem

Theorem 2.6: for a continuous `f`, computability (the graph is r.e.) is
equivalent both to combinatory definability of its graph and to closed
LAMBDA-definability.  The appendix proves the key converse
`IsRE u → IsCombinatory u` by realizing primitive recursion and enumerating
an arbitrary r.e. set.
-/

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Recursively enumerable subsets of `ω`, as elements of `Pω`. -/
def IsRE (u : Pomega) : Prop :=
  REPred fun n : ℕ => n ∈ u

/-- **Scott 1976, §2, Definition.** A continuous `k`-ary map is computable
when membership in its values on finite arguments is r.e. Unary case: -/
def IsComputable (f : Pomega → Pomega) : Prop :=
  IsScottContinuous f ∧ IsRE (graph f)

/-- Closed LAMBDA-definable elements (empty environment). -/
def IsLambdaDefinable (u : Pomega) : Prop :=
  ∃ t : Term, interp t (fun _ => botElem) = u

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

def pack4 (n0 n1 n2 m : ℕ) : ℕ :=
  Nat.pair n0 (Nat.pair n1 (Nat.pair n2 m))

def pack4_proj1 (t : ℕ) : ℕ := (Nat.unpair t).1
def pack4_proj2 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair t).2).1
def pack4_proj3 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1
def pack4_proj4 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2


/-- **Scott 1976, (2.16).** Combinator for `λx. 0 ∪ (x+1)`. -/
def topRecTerm : Term :=
  .lam 0 (.cond (.lam 1 .zero) .zero (.succ (.var 0)))

/-- A combinator realizes a number-theoretic function on numerals. -/
def Realizes (u : Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n, funOf u (ofNat n) = ofNat (p n)

def Realizes2 (u : Pomega) (p : ℕ → ℕ → ℕ) : Prop :=
  ∀ n m, funOf (funOf u (ofNat n)) (ofNat m) = ofNat (p n m)

def composeC (u v : Pomega) : Pomega :=
  funOf (funOf Scomb (funOf Kcomb u)) v

def constComb (k : ℕ) : Pomega := funOf Kcomb (ofNat k)

/-- Scott (2.27) packaged as a combinator. -/
def primRecComb (a f : Pomega) : Pomega :=
  funOf dollarC
    (funOf Ycomb
      (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f))

def addStepC : Pomega := funOf Kcomb sucC

/-- `λx. primRecComb x (K suc)`. -/
def addC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb (interp primRecStepTerm (fun _ => botElem)))
        (funOf Kcomb addStepC)))

/-- `λx. x ⊃ 0, x−1`, so numerals stay numerals. -/
def safePredC : Pomega :=
  interp (.lam 0 (.cond (.var 0) .zero (.pred (.var 0)))) (fun _ => botElem)

def subStepC : Pomega := funOf Kcomb safePredC

def subC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb (interp primRecStepTerm (fun _ => botElem)))
        (funOf Kcomb subStepC)))

/-- `λx. primRecComb 0 (K (addC x))`. -/
def mulC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb
          (funOf Kcomb
            (funOf (interp primRecStepTerm (fun _ => botElem)) (ofNat 0))))
        (funOf (funOf Scomb (funOf Kcomb Kcomb)) addC)))

/-- `cond 1 0 n` is `1` on `0` and `0` on positive numerals. -/
def isZeroC : Pomega := funOf (funOf condC (ofNat 1)) (ofNat 0)

/-- `λn λm. isZero (n − m)`. -/
def leC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ (Scomb ⬝ (Kcomb ⬝ isZeroC))) ⬝ subC

/-- `λa λb. (b-a) ⊃ (a*a+a+b), (b*b+a)` with free `add, mul, sub`. -/
def pairTerm : Term :=
  .lam 3 (.lam 4
    (.cond (.app (.app (.var 2) (.var 4)) (.var 3))
      (.app (.app (.var 0)
          (.app (.app (.var 0)
              (.app (.app (.var 1) (.var 3)) (.var 3)))
            (.var 3)))
        (.var 4))
      (.app (.app (.var 0)
          (.app (.app (.var 1) (.var 4)) (.var 4)))
        (.var 3))))

def arithEnv : ℕ → Pomega
  | 0 => addC
  | 1 => mulC
  | 2 => subC
  | _ => botElem

def pairComb : Pomega := interp pairTerm arithEnv

/-! ### The appendix converse: primitive-recursive realizability -/

/-- Primitive recursion with zero initial value, viewed as an operator on its step. -/
def primRecZeroC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ dollarC) ⬝
    (Scomb ⬝ (Kcomb ⬝ Ycomb) ⬝
      (interp primRecStepTerm (fun _ => botElem) ⬝ ofNat 0))

/-- The bounded iteration used to compute `Nat.sqrt n`. -/
def sqrtIter (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      let a := sqrtIter n k
      if (a + 1) * (a + 1) ≤ n then a + 1 else a

def sqrtEnv : ℕ → Pomega
  | 3 => leC
  | 4 => mulC
  | _ => botElem

/-- `λn _ a. if (a+1)^2 ≤ n then a+1 else a`. -/
def sqrtStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond
      (.app (.app (.var 3)
        (.app (.app (.var 4) (.succ (.var 2))) (.succ (.var 2))))
        (.var 0))
      (.var 2)
      (.succ (.var 2)))))

def sqrtStepC : Pomega := interp sqrtStepTerm sqrtEnv

/-- A combinator realizing integer square root. -/
def sqrtC : Pomega :=
  Scomb ⬝
    (Scomb ⬝ (Kcomb ⬝ primRecZeroC) ⬝ sqrtStepC) ⬝
    (Scomb ⬝ Kcomb ⬝ Kcomb)

def unpairEnv : ℕ → Pomega
  | 1 => sqrtC
  | 2 => subC
  | 3 => mulC
  | 4 => leC
  | _ => botElem

def unpairSqrtTerm : Term := .app (.var 1) (.var 0)
def unpairSquareTerm : Term :=
  .app (.app (.var 3) unpairSqrtTerm) unpairSqrtTerm
def unpairDeltaTerm : Term :=
  .app (.app (.var 2) (.var 0)) unpairSquareTerm
def unpairTestTerm : Term :=
  .app (.app (.var 4) (.succ unpairDeltaTerm)) unpairSqrtTerm

def unpairFstTerm : Term :=
  .lam 0 (.cond unpairTestTerm unpairSqrtTerm unpairDeltaTerm)

def unpairSndTerm : Term :=
  .lam 0 (.cond unpairTestTerm
    (.app (.app (.var 2) unpairDeltaTerm) unpairSqrtTerm)
    unpairSqrtTerm)

def unpairFstC : Pomega := interp unpairFstTerm unpairEnv
def unpairSndC : Pomega := interp unpairSndTerm unpairEnv

/-- Curried operator `λa f. primRecComb a f`. -/
def primRecOpEnv : ℕ → Pomega
  | 2 => dollarC
  | 3 => Ycomb
  | 4 => interp primRecStepTerm (fun _ => botElem)
  | _ => botElem

def primRecOpTerm : Term :=
  .lam 0 (.lam 1
    (.app (.var 2)
      (.app (.var 3) (.app (.app (.var 4) (.var 0)) (.var 1)))))

def primRecOpC : Pomega := interp primRecOpTerm primRecOpEnv

def pairRealizer (u v : Pomega) : Pomega :=
  Scomb ⬝ (Scomb ⬝ (Kcomb ⬝ pairComb) ⬝ u) ⬝ v

/-- Environment for the primitive-recursion constructor of `Nat.Primrec`. -/
def precEnv (f g : Pomega) : ℕ → Pomega
  | 3 => primRecOpC
  | 4 => f
  | 5 => g
  | 6 => unpairFstC
  | 7 => unpairSndC
  | 8 => pairComb
  | _ => botElem

/-- On packed input `(z,n)`, recurse from `f z` with
step `λy ih. g (pair z (pair y ih))`. -/
def precTerm : Term :=
  .lam 0
    (.app
      (.app
        (.app (.var 3) (.app (.var 4) (.app (.var 6) (.var 0))))
        (.lam 1 (.lam 2
          (.app (.var 5)
            (.app (.app (.var 8) (.app (.var 6) (.var 0)))
              (.app (.app (.var 8) (.var 1)) (.var 2)))))))
      (.app (.var 7) (.var 0)))

def precC (f g : Pomega) : Pomega := interp precTerm (precEnv f g)

/-- Stage-bounded enumerator associated to a partial-recursive code. -/
def enumFun (c : Code) (t : ℕ) : ℕ :=
  bif (evaln t.unpair.2 c t.unpair.1).isSome
    then t.unpair.1 + 1
    else 0

def enumRangeC (r : Pomega) : Pomega :=
  (dollarC ⬝ r) ⬝ topElem

/-- **Scott 1976, §2, Definition.** A `k`-ary continuous map is computable
when its nested graph (the pairing encoding of
`m ∈ f(e n₀)⋯(e n_{k-1})`) is r.e. -/
def IsComputableFin {n : ℕ} (f : (Fin n → Pomega) → Pomega) : Prop :=
  IsScottContinuousFin f ∧ IsRE (curryFin f)
end DomainTheory.DataTypesAsLattices
