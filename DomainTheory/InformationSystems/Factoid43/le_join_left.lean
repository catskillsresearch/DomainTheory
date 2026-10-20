/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Factoid35
public import DomainTheory.InformationSystems.Factoid42
public import DomainTheory.InformationSystems.Factoid43.Basic
public import DomainTheory.InformationSystems.Factoid43.subset_deductiveClosure

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)







theorem le_join_left (x y : sys.Element)
    (h : sys.IsFinitelyConsistent (x.carrier ∪ y.carrier)) : x ≤ sys.join x y h :=
  fun _a ha => sys.subset_deductiveClosure _ h (Or.inl ha)

end InfoSys
end DomainTheory.InformationSystems
