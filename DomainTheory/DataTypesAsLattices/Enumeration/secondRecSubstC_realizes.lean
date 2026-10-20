/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices












































theorem secondRecSubstC_realizes : Realizes secondRecSubstC secondRecSubst :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose_spec.2

end DomainTheory.DataTypesAsLattices
