module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def pairTerm : Term :=
  .lam 3 (.lam 4
    (.cond (.app (.app (.var 2) (.var 4)) (.var 3))
      (.app (.app (.var 0)
          (.app (.app (.var 0)
              (.app (.app (.var 1) (.var 3)) (.var 3)))
            (.var 3)))
        (.var 4))
      (.app (.app (.var 0)
          (.app (.app (.var 1) (.var 4)) (.var 4)))
        (.var 3))))


open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairSqrtTerm : Term := .app (.var 1) (.var 0)

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairSquareTerm : Term :=
  .app (.app (.var 3) unpairSqrtTerm) unpairSqrtTerm

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairDeltaTerm : Term :=
  .app (.app (.var 2) (.var 0)) unpairSquareTerm

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairTestTerm : Term :=
  .app (.app (.var 4) (.succ unpairDeltaTerm)) unpairSqrtTerm

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairFstTerm : Term :=
  .lam 0 (.cond unpairTestTerm unpairSqrtTerm unpairDeltaTerm)

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairSndTerm : Term :=
  .lam 0 (.cond unpairTestTerm
    (.app (.app (.var 2) unpairDeltaTerm) unpairSqrtTerm)
    unpairSqrtTerm)

end DomainTheory.DataTypesAsLattices
