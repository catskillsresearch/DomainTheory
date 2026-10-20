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
import DomainTheory.Neighborhood.Exercise813c.generatedBy_genPoint_isClopen
import DomainTheory.Neighborhood.Exercise813c.generatedBy_genPoint_box


namespace DomainTheory.Neighborhood








theorem isOpen_box (I : Finset ℕ) (f : ℕ → Bool) : IsOpen (box I f) :=
  (generatedBy_genPoint_isClopen (generatedBy_genPoint_box I f)).isOpen

end DomainTheory.Neighborhood
