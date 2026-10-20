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
public import DomainTheory.InformationSystems.Factoid43.IsFinitelyConsistent
public import DomainTheory.InformationSystems.Factoid43.deductiveClosure
public import DomainTheory.InformationSystems.Factoid43.familyUnionCarrier

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Join of a family whose carrier-union is finitely consistent. -/
def familySup (S : Set sys.Element)
    (hU : sys.IsFinitelyConsistent (sys.familyUnionCarrier S)) : sys.Element :=
  sys.deductiveClosure (sys.familyUnionCarrier S) hU

end InfoSys

end DomainTheory.InformationSystems
