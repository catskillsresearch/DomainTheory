/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Proposition56

@[expose] public section

/-!
# Factoid 7.6 — combinators as approximable operators

**Scott 1982 (*Higher-type functions and the combinators*).** Once function spaces
exist as domains, the familiar combinators become approximable operators:

* `const : B → (A → B)` with `const(b) = constMap b`
* `pair : (C → A) × (C → B) → (C → A × B)` with `pair(f, g) = ⟨f, g⟩`
* `comp : (B → C) × (A → B) → (A → C)` with `comp(g, f) = g ∘ f`

Each is obtained by currying a composite of `apply`, `fst`/`snd`, and `pair`
(already approximable), so approximability is immediate.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-! ## Helpers: pairing with projections -/

/-! ## `const : B → (A → B)` -/

/-- **Factoid 7.6.** Operator `const : B → (A → B)`, as `curry fst`. -/
def constOp : ApproximableMap B (functionSystem A B) :=
  curryMap B A B (fstMap B A)

/-! ## `pair : (C → A) × (C → B) → (C → A × B)` -/

/-- Uncurried pairing: `((C→A)×(C→B)) × C → A×B`. -/
def pairOpUncurry : ApproximableMap
    (productSystem (productSystem (functionSystem C A) (functionSystem C B)) C)
    (productSystem A B) :=
  let P := productSystem (functionSystem C A) (functionSystem C B)
  pairMap A B
    (comp (applyMap (B := C) (C := A))
      (pairMap (functionSystem C A) C
        (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
        (sndMap P C)))
    (comp (applyMap (B := C) (C := B))
      (pairMap (functionSystem C B) C
        (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
        (sndMap P C)))

/-- **Factoid 7.6.** Operator `pair : (C → A) × (C → B) → (C → A × B)`. -/
def pairOp : ApproximableMap
    (productSystem (functionSystem C A) (functionSystem C B))
    (functionSystem C (productSystem A B)) :=
  curryMap (productSystem (functionSystem C A) (functionSystem C B)) C (productSystem A B)
    (pairOpUncurry A B C)

/-! ## `comp : (B → C) × (A → B) → (A → C)` -/

/-- Uncurried composition: `((B→C)×(A→B)) × A → C`. -/
def compOpUncurry : ApproximableMap
    (productSystem (productSystem (functionSystem B C) (functionSystem A B)) A) C :=
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B
      (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
      (comp (applyMap (B := A) (C := B))
        (pairMap (functionSystem A B) A
          (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (sndMap Q A))))

/-- **Factoid 7.6.** Operator `comp : (B → C) × (A → B) → (A → C)`. -/
def compOp : ApproximableMap
    (productSystem (functionSystem B C) (functionSystem A B))
    (functionSystem A C) :=
  curryMap (productSystem (functionSystem B C) (functionSystem A B)) A C
    (compOpUncurry A B C)
end InfoSys
end DomainTheory.InformationSystems
