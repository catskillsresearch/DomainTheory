/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.unitElement_eq_bot

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}

/-- There is a unique approximable map into `1`, namely `const(⊥_1)`. -/
theorem approxMap_to_unit_eq_const (f : ApproximableMap A unitSystem) :
    f = constMap (A := A) unitSystem.botElement :=
  constMap_unique unitSystem.botElement f fun x => unitElement_eq_bot (f.toElement x)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
