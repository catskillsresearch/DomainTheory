module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.IsComputable
public import DomainTheory.DataTypesAsLattices.Computability.LambdaDefinable
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj1
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj2
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj3
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj4
public import DomainTheory.DataTypesAsLattices.Computability.topRecTerm
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.Realizes2
public import DomainTheory.DataTypesAsLattices.Computability.composeC
public import DomainTheory.DataTypesAsLattices.Computability.constComb
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Computability.addStepC
public import DomainTheory.DataTypesAsLattices.Computability.addC
public import DomainTheory.DataTypesAsLattices.Computability.safePredC
public import DomainTheory.DataTypesAsLattices.Computability.subStepC
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Computability.pairTerm
public import DomainTheory.DataTypesAsLattices.Computability.arithEnv
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtIter
public import DomainTheory.DataTypesAsLattices.Computability.sqrtEnv
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepTerm
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC
public import DomainTheory.DataTypesAsLattices.Computability.unpairEnv
public import DomainTheory.DataTypesAsLattices.Computability.unpairSqrtTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairSquareTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairDeltaTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairTestTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpEnv
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpTerm
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC
public import DomainTheory.DataTypesAsLattices.Computability.pairRealizer
public import DomainTheory.DataTypesAsLattices.Computability.precEnv
public import DomainTheory.DataTypesAsLattices.Computability.precTerm
public import DomainTheory.DataTypesAsLattices.Computability.precC
public import DomainTheory.DataTypesAsLattices.Computability.enumFun
public import DomainTheory.DataTypesAsLattices.Computability.enumRangeC
public import DomainTheory.DataTypesAsLattices.Computability.ComputableFin
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb_ofNat
public import DomainTheory.DataTypesAsLattices.Computability.pairComb_app
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem precC_realizes {f g : Pomega} {p q : ℕ → ℕ}
    (hf : Realizes f p) (hg : Realizes g q) :
    Realizes (precC f g)
      (Nat.unpaired fun z n => n.rec (p z) fun y ih => q (Nat.pair z (Nat.pair y ih))) := by
  intro w
  rw [precC, precTerm, theorem_2_2_beta]
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (6 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (7 : ℕ) ≠ 0),
    precEnv]
  simp [Function.update]
  rw [unpairFstC_realizes, unpairSndC_realizes, hf, primRecOpC_app,
    primRecComb_ofNat]
  let z := w.unpair.1
  let step : Pomega :=
    interp (.lam 1 (.lam 2
      (.app (.var 5)
        (.app (.app (.var 8) (ofNat z |> fun _ => .app (.var 6) (.var 0)))
          (.app (.app (.var 8) (.var 1)) (.var 2))))))
      (Function.update (precEnv f g) 0 (ofNat w))
  have hstep (y ih : ℕ) :
      (step ⬝ ofNat y) ⬝ ofNat ih =
        ofNat (q (Nat.pair z (Nat.pair y ih))) := by
    dsimp [step, z]
    rw [theorem_2_2_beta, theorem_2_2_beta]
    simp [interp, envSet, Function.update, precEnv]
    rw [unpairFstC_realizes, pairComb_app, pairComb_app, hg]
  have hrec : ∀ n,
      primRecVal (ofNat (p z)) step n =
        ofNat (n.rec (p z) fun y ih => q (Nat.pair z (Nat.pair y ih))) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (step ⬝ ofNat n) ⬝ primRecVal (ofNat (p z)) step n = _
      rw [ih, hstep]
  exact hrec w.unpair.2

end DomainTheory.DataTypesAsLattices
