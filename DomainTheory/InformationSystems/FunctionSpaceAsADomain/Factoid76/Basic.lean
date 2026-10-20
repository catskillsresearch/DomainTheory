/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.constOp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOpUncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOpUncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOp

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


/-! ## `pair : (C → A) × (C → B) → (C → A × B)` -/



/-! ## `comp : (B → C) × (A → B) → (A → C)` -/


end InfoSys
end DomainTheory.InformationSystems
