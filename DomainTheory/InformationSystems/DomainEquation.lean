/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid81
import DomainTheory.InformationSystems.Factoid82

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
