/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Factoid83.VToken
public import DomainTheory.InformationSystems.Factoid83.VEnt
public import DomainTheory.InformationSystems.Factoid83.VEnt
public import DomainTheory.InformationSystems.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.Factoid83.IsUToken

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

instance : DecidablePred IsUToken := fun t =>
  if h : t = .top then isFalse fun ht => ht h
  else isTrue h

end InfoSys

end DomainTheory.InformationSystems
