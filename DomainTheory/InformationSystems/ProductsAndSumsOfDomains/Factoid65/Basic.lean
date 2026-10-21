/-ai
This file gathers and re-exports approximable maps, the least element of a domain, and the unit information system. Scott's Factoid 6.5 says that the trivial product of no factors is the unit system, whose only token is least-informative and whose only element is the least element, that every approximable map out of the unit is constant, and that the unique approximable map into the unit is the constant map at that least element.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Factoid65.unitSystem

@[expose] public section

/-!
# Factoid 6.5 — the unit domain

**Scott 1982 (end of §6, after Prop 6.2).** The trivial product of no factors is the
*unit* information system `1` with `D_1 = {Δ_1}`. It has a unique element `⊥_1`.
Every approximable map `1 → A` is constant, and there is a unique approximable map
`A → 1`, namely `const(⊥_1)`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
