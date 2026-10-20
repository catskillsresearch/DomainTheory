module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.DomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.scottCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatRel
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_topElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.BotApprox_any
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatRel_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_refl
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_toElement_of_mem_one
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_rogue
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_consistent
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_idem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_isDomain

@[expose] public section

/-!
# Factoid 8.4 — a domain of domains (Scott’s sketch)

**Scott 1982, §8 (final remark).** Scott is deliberately sketchy: finite information
about a domain is packaged as an approximable map `r : P → P` on the powerset
domain `P` of the non-negative integers (with `0` as `Δ` and `1` as a reserved
rogue like `∇`). The maps satisfying (1)–(5) below are exactly the *elements* of
the domain of domains; the token-level InfoSys is said to arise from
`(P → P)` by a construction “similar to” `U` from `V`, with details deferred.

We formalize `P`, state (1)–(5) on `ApproximableMap P P`, package
`DomainApprox`, record Scott’s consistency remark, and exhibit one inhabitant
(the “flat” map that treats `1` as rogue). Functors-as-approximable-maps and
powerdomains are left external, as in the source.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84

/-! ## The powerset domain `P` (Scott) -/





/-! ## Scott’s conditions (1)–(5) on `r : P → P` -/




/-! ## (3) is automatic for any approximable map -/


/-! ## Example: flat domain map (treat `1` as rogue) -/











/-! ## Identity fails (4): `I_P` is not a domain map -/
end Factoid84
end DomainTheory.InformationSystems
