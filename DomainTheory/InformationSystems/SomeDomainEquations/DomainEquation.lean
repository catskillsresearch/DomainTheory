/-ai
This file gathers and re-exports the first two constructions of Scott's Section 8. Factoid 8.1 is the tree information system solving the equation of a domain with the separated sum of an atom system and the product of the domain with itself. Factoid 8.2 is the lambda information system solving the equation of a domain with the separated sum of an atom system and the function space of the domain into itself.
ai-/
module

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82

@[expose] public section

/-!
# Domain equations — Section 8

Thin re-export of the first two §8 constructions:

* Factoid 8.1 (`Factoid81.lean`): `treeSystem` solves `T ≅ A + (T × T)`.
* Factoid 8.2 (`Factoid82.lean`): `lambdaSystem` solves `D ≅ A + (D → D)`.

Factoids 8.3–8.4 (`Factoid83.lean`, `Factoid84.lean`) are independent modules
(imported from the library root `DomainTheory.InformationSystems.lean`); they do not depend on this file.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

-- Factoid 8.1: see Factoid81.lean (`treeSystem`, `treeUnfold`, `treeRhs`)
-- Factoid 8.2: see Factoid82.lean (`lambdaSystem`, `lamUnfold`, `lamRhs`)
-- Factoid 8.3–8.4: see Factoid83.lean / Factoid84.lean (not re-exported here)

end InfoSys

end DomainTheory.InformationSystems
