module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.addC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.subC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.mulC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

















theorem arithEnv_combinatory : ∀ i, IsCombinatory (arithEnv i)
  | 0 => addC_combinatory
  | 1 => mulC_combinatory
  | 2 => subC_combinatory
  | n + 3 => by
    have hbot : funOf predC zeroC = botElem := by
      rw [predC_app]; exact eq_2_6
    simpa [arithEnv, hbot] using
      IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

end DomainTheory.DataTypesAsLattices
