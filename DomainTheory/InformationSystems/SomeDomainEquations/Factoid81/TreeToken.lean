/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
universe u

/-- Tokens of the tree system: sum tagging of atoms and product left/right copies. -/
inductive TreeToken (α : Type u) where
  | bot : TreeToken α
  | atom : α → TreeToken α
  | pairL : TreeToken α → TreeToken α
  | pairR : TreeToken α → TreeToken α

instance instDecidableEqTreeToken {α : Type u} [DecidableEq α] :
    DecidableEq (TreeToken α)
  | .bot, .bot => isTrue rfl
  | .atom a, .atom b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (TreeToken.atom.inj h')
  | .pairL a, .pairL b =>
      match instDecidableEqTreeToken a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun h' => h (TreeToken.pairL.inj h')
  | .pairR a, .pairR b =>
      match instDecidableEqTreeToken a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun h' => h (TreeToken.pairR.inj h')
  | .bot, .atom _ => isFalse fun h => nomatch h
  | .bot, .pairL _ => isFalse fun h => nomatch h
  | .bot, .pairR _ => isFalse fun h => nomatch h
  | .atom _, .bot => isFalse fun h => nomatch h
  | .atom _, .pairL _ => isFalse fun h => nomatch h
  | .atom _, .pairR _ => isFalse fun h => nomatch h
  | .pairL _, .bot => isFalse fun h => nomatch h
  | .pairL _, .atom _ => isFalse fun h => nomatch h
  | .pairL _, .pairR _ => isFalse fun h => nomatch h
  | .pairR _, .bot => isFalse fun h => nomatch h
  | .pairR _, .atom _ => isFalse fun h => nomatch h
  | .pairR _, .pairL _ => isFalse fun h => nomatch h

end InfoSys
end DomainTheory.InformationSystems
