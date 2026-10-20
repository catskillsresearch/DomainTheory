/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise813b
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen
import DomainTheory.Neighborhood.Exercise813c.Basic
import DomainTheory.Neighborhood.Exercise813c.isClopen_genPoint


namespace DomainTheory.Neighborhood





theorem isOpen_genPoint (i : ℕ) : IsOpen (genPoint i) := (isClopen_genPoint i).isOpen

end DomainTheory.Neighborhood
