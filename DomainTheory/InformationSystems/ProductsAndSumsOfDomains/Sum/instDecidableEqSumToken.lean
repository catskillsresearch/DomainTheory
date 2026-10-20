/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

instance instDecidableEqSumToken : DecidableEq (SumToken α β)
  | .left a, .left b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.left.inj h')
  | .right a, .right b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.right.inj h')
  | .bot, .bot => isTrue rfl
  | .left _, .right _ => isFalse fun h => nomatch h
  | .left _, .bot => isFalse fun h => nomatch h
  | .right _, .left _ => isFalse fun h => nomatch h
  | .right _, .bot => isFalse fun h => nomatch h
  | .bot, .left _ => isFalse fun h => nomatch h
  | .bot, .right _ => isFalse fun h => nomatch h

end InfoSys

end DomainTheory.InformationSystems
