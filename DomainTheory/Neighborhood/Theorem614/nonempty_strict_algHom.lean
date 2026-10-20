/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition613
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem614.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w

namespace Theorem614


variable {α : Type w}



































theorem nonempty_strict_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (colimAlg s) B // IsStrict g.hom} :=
  nonempty_algHom_of_continuousOnMaps s.T s.hmaps (colimIso s) B hk

end Theorem614
end DomainTheory.Neighborhood
